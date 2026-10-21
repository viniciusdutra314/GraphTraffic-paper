using GraphTraffic
using GraphTraffic.orchestrator: Experiment,
    run_simulation, run_analysis, run_visualization
import GraphTraffic.orchestrator: simulation, analysis, visualization
using Graphs
using DataFrames: DataFrame
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
    η_values=logrange(1e-2, 1.0, 20)
    rho_values=logrange(1e-2, 1.0, 10)
    iterations=10_000
    warmup=1000
    free_flow_sampling_time=200
    configs=[SimulationConfig(; graph, message_rate, iterations, warmup,
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
                avg_capacity=average_edge_capacity(result)
            )
        )
    end
    DataFrame(rows)
end

function visualization(::Type{RhoVsEta},
    table::AbstractDataFrame;
    directory::AbstractString, num_threads::Integer=1)

    fig = Figure(size=(1500, 1500))

    positions=[((1, 1), (1, 2)), ((1, 3), (1, 4)), ((2, 1), (2, 2)), ((2, 3), (2, 4))]
    for (graph_table, (msg_position, capacity_position)) in zip(groupby(table, :graph_name; sort=true), positions)

        ax_messages = Axis(fig[msg_position...];
            title=first(graph_table.graph_name),
            xlabel="ρ",
            ylabel="Mensagens na rede ao final",
            xscale=log10,
            yscale=log10
        )
        ax_capacity = Axis(fig[capacity_position...];
            title=first(graph_table.graph_name),
            xlabel="ρ",
            ylabel="Capacidade média",
            xscale=log10,
            yscale=log10
        )
        for eta_table in groupby(graph_table, :eta; sort=true)
            # A ordem das linhas da análise não determina a ordem da curva.
            points = sort(eta_table, :rho)

            scatterlines!(ax_messages, points.rho, points.total_messages_mean;
                label="η = $(first(points.eta))",
            )
            scatterlines!(ax_capacity, points.rho, points.avg_capacity;
                label="η = $(first(points.eta))",
            )

        end

        axislegend(ax_messages; position=:lt)
    end
    save(joinpath(directory, "eta-vs-rho.svg"), fig)
    nothing
end
