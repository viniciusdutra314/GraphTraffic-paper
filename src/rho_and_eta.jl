using GraphTraffic
using GraphTraffic.orchestrator: Experiment,
    run_simulation, run_analysis, run_visualization
import GraphTraffic.orchestrator: simulation, analysis, visualization
using Graphs
using DataFrames
using GraphTraffic.Topology
using CairoMakie
using JSON
using StatsBase
using Random: MersenneTwister

struct RhoVsEta <: Experiment end

function simulation(::Type{RhoVsEta};
    output::AbstractString, num_threads::Integer, overwrite::Bool)
    N=1000
    E=2000
    β=1e-1
    graphs_and_names=[
        ("barabasi", barabasi_albert(N, E ÷ N)),
        ("erdos", erdos_renyi(N, E)),
        ("watts", watts_strogatz_given_m(N, E, β)),
        ("geometric", random_geometric_graph(N, E))
    ]
    foreach(x->make_graph_connected!(x[2]), graphs_and_names)
    η_values=logrange(1e-2, 1.0, 10)
    rho_values=logrange(1e-3, 1e-1, 10)
    iterations=10_000
    warmup=1000
    free_flow_sampling_time=200
    routing=RandomWalk()
    configs=[SimulationConfig(; graph, routing, message_rate, iterations, warmup,
        initial_capacity=uniform_initial_capacity(graph, 1), modifiers=[
        ModifierEdgeCapacity(; free_flow_rate, free_flow_sampling_time)
    ],
        metadata=JSON.Object{String,Any}(
            "graph_name" => graph_name,
            "eta" => free_flow_rate,
        ),
        observers=[ObserverTotalMessages(), ObserverEdgeCapacity(; update_interval=free_flow_sampling_time)]) for (graph_name, graph) in graphs_and_names for free_flow_rate in η_values for message_rate in rho_values]
    call_graphtraffic_rs(configs; output, num_threads, overwrite)
    nothing

end

function analysis(::Type{RhoVsEta},
    results::AbstractDict{SimulationID,SimulationResult};
    num_threads::Integer=1)
    rows = NamedTuple[]
    for result in values(results)
        messages=result.total_messages
        tail=messages[(end-length(messages)÷10):end]
        push!(rows,
            (graph_name=GraphTraffic.original_json_config(result)["metadata"]["graph_name"],
                rho=result.message_rate,
                eta=GraphTraffic.original_json_config(result)["metadata"]["eta"],
                total_messages_mean=mean(tail),
                total_messages_std=std(tail),
                avg_capacity=average_edge_capacity(result),
                average_traveling_time=result.average_traveling_time
            )
        )
    end
    DataFrame(rows)
end

function visualization(::Type{RhoVsEta},
    table::AbstractDataFrame;
    directory::AbstractString, num_threads::Integer=1)

    fig = Figure(size=(1600, 1800), fontsize=17, backgroundcolor=:white)
    Label(fig[0, 1:2], "RANDOM WALK"; fontsize=30, font=:bold,
        padding=(0, 0, 12, 0))

    eta_values = sort(unique(table.eta))
    # Uma faixa opaca por η, com mudanças de matiz em vez de tons esbranquiçados.
    # O intervalo global mantém a mesma cor para o mesmo η em todos os grafos.
    colormap = cgrad(:turbo, length(eta_values); categorical=true)
    # Os valores simulados são categorias globais: cada tick fica no centro
    # de sua faixa, sem interpolar valores de η que não foram simulados.
    color_range = (0.5, length(eta_values) + 0.5)
    graph_titles = Dict("barabasi" => "Barabási–Albert", "erdos" => "Erdős–Rényi",
        "geometric" => "Geométrico", "watts" => "Watts–Strogatz")
    for (index, graph_table) in enumerate(groupby(table, :graph_name; sort=true))
        panel = fig[index, 1] = GridLayout()
        graph_name = first(graph_table.graph_name)
        Label(panel[0, 1:3], graph_titles[graph_name]; fontsize=21, font=:bold)

        axis_style = (; xscale=log10, yscale=log10,
            xgridcolor=(:black, 0.07), ygridcolor=(:black, 0.07),
            xgridstyle=:dash, ygridstyle=:dash,
            topspinevisible=false, rightspinevisible=false,
            titlefont=:regular, titlesize=17)
        ax_messages = Axis(panel[1, 1];
            title="Mensagens na rede",
            xlabel="ρ",
            ylabel="Média ao final",
            axis_style...
        )
        ax_capacity = Axis(panel[1, 2];
            title="Capacidade das arestas",
            xlabel="ρ",
            ylabel="Capacidade média",
            axis_style...
        )
        ax_traveling_time = Axis(panel[1, 3];
            title="Tempo médio de viagem",
            xlabel="ρ",
            ylabel="Tempo médio (iterações)",
            axis_style...,
            yscale=identity,
        )
        for eta_table in groupby(graph_table, :eta; sort=true)
            # A ordem das linhas da análise não determina a ordem da curva.
            points = sort(eta_table, :rho)

            # O índice vem da lista global, nunca da ordem local dos grupos.
            eta_index = searchsortedfirst(eta_values, first(points.eta))
            color_style = (; color=fill(eta_index, nrow(points)),
                colormap, colorrange=color_range,
                alpha=1.0, linewidth=2.2, markersize=6)
            scatterlines!(ax_messages, points.rho, points.total_messages_mean;
                color_style...)
            scatterlines!(ax_capacity, points.rho, points.avg_capacity;
                color_style...)
            scatterlines!(ax_traveling_time, points.rho, points.average_traveling_time;
                color_style...)

        end

        linkxaxes!(ax_messages, ax_capacity, ax_traveling_time)
        colgap!(panel, 20)
    end
    Colorbar(fig[1:length(groupby(table, :graph_name)), 2]; colormap, limits=color_range,
        ticks=(collect(eachindex(eta_values)), string.(round.(eta_values; sigdigits=3))),
        label="η", width=20, ticklabelsize=14, labelsize=20, spinewidth=0)
    rowgap!(fig.layout, 35)
    colgap!(fig.layout, 45)
    mkpath(directory)
    save(joinpath(directory, "eta-vs-rho.svg"), fig)
    nothing
end
