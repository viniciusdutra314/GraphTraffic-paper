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

struct MomentumVsCapacity <: Experiment end

function simulation(::Type{MomentumVsCapacity}; output::AbstractString,
                        num_threads::Integer, overwrite::Bool)
     N=1_000 
     E=2_000 
     β=0.1
                        graphs=[
        ("barabasi", "Barabási–Albert", barabasi_albert(N,E ÷ N)),
        ("erdos", "Erdős–Rényi", erdos_renyi(N,E)),
        ("watts", "Watts–Strogatz (β=$β)", watts_strogatz_given_m(N,E,β)),
        ("geometric", "Random geometric", random_geometric_graph(N,E))
    ]
    for (_,_,graph) in graphs
        make_graph_connected!(graph)
    end
    message_rate=0.2
    iterations=10_000
    warmup=1_000
    free_flow_rate=0.90
    free_flow_sampling_time=500
    repetitions=10
    α_values=range(0.0,0.5,10)
    configs=[
        SimulationConfig(;graph,message_rate,
        initial_capacity=uniform_initial_capacity(graph,1),iterations,warmup,
        modifier=ModifierEdgeCapacity(;free_flow_rate,free_flow_sampling_time,momentum),
        observers=[ObserverEdgeCapacity(update_interval=free_flow_sampling_time),ObserverFreeFlowRate()],
        metadata=JSON.Object{String,Any}("graph_name"=>graph_name,
            "graph_label"=>graph_label,"momentum"=>momentum))
        for (graph_name,graph_label,graph) in graphs
        for momentum in α_values for _ in 1:repetitions
    ]
    call_graphtraffic_rs(configs;output,num_threads,overwrite)
end

function analysis(::Type{MomentumVsCapacity},
    results::AbstractDict{SimulationID,SimulationResult};
    num_threads::Integer=1)
    rows=NamedTuple[]
    for result in values(results)
        config=GraphTraffic.original_json_config(result)
        modifier=config["modifier"]
        push!(rows,(
            graph_name=config["metadata"]["graph_name"],
            graph_label=config["metadata"]["graph_label"],
            N=length(GraphTraffic.read_dataset(result,"vertices_attributes")),
            E=length(GraphTraffic.read_dataset(result,"edges_attributes")),
            iterations=config["max_iterations"],
            warmup=config["warm_up_iterations"],
            message_rate=config["message_generation"],
            free_flow_rate=modifier["free_flow_rate"],
            free_flow_sampling_time=modifier["free_flow_sampling_time"],
            mean_capacity=average_edge_capacity(result),
            momentum=config["metadata"]["momentum"],
            average_traveling_time=result.average_traveling_time,
            avg_free_flow=mean(row.free_flow_times / row.num_samples for row in free_flow_counts(result))
        ))
    end
    table = DataFrame(rows)
    summary = combine(
        groupby(table, [:graph_name, :graph_label, :momentum, :N, :E, :iterations, :warmup, :message_rate,
                        :free_flow_rate, :free_flow_sampling_time]),
        nrow => :repetitions,
        :mean_capacity => mean => :mean_capacity,
        :mean_capacity => std  => :std_capacity,
        :average_traveling_time => mean => :average_traveling_time,
        :avg_free_flow => mean => :avg_free_flow
    )
    sort!(summary, [:graph_name, :momentum])
    return summary
end

function visualization(::Type{MomentumVsCapacity}, table::AbstractDataFrame;
    directory::AbstractString, num_threads::Integer=1)
    graph_tables=groupby(table,:graph_name;sort=true)
    fig=Figure(size=(1000,1200))
    for (row,graph_table) in enumerate(graph_tables)
        panel=fig[row,1]=GridLayout()
        points=sort(graph_table,:momentum)
        graph_name=first(points.graph_name)
        color=graph_type_to_colors[graph_name == "geometric" ? "geometrico" : graph_name]
        config=first(points)
        Label(panel[0,1:4],
            "$(config.graph_label) | N=$(config.N) | E=$(config.E) | iterations=$(config.iterations) | warmup=$(config.warmup)\n" *
            "message_rate=$(config.message_rate) | free_flow_rate=$(config.free_flow_rate) | free_flow_sampling_time=$(config.free_flow_sampling_time) | repetitions=$(config.repetitions)";
            fontsize=16)
        ax_capacity_mean=Axis(panel[1,1],xlabel="Momentum",ylabel="Capacidade média")
        ax_capacity_std=Axis(panel[1,2],xlabel="Momentum",ylabel="sigma/mu")
        ax_travelling=Axis(panel[1,3],xlabel="Momentum",ylabel="Average travelling time")
        ax_free_flow=Axis(panel[1,4],xlabel="Momentum",ylabel="Observered Average Free Flow")
        scatter!(ax_capacity_mean,points.momentum,points.mean_capacity;color)
        scatter!(ax_capacity_std,points.momentum,points.std_capacity ./ points.mean_capacity;color)
        scatter!(ax_travelling,points.momentum,points.average_traveling_time;color)
        scatter!(ax_free_flow,points.momentum,points.avg_free_flow;color)
    end
    save(joinpath(directory,"momentum-vs-capacity.svg"),fig)
    nothing
end
