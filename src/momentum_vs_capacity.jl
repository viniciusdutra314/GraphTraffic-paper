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
                        num_threads::Integer,
                        overwrite::Bool)
    N=1_000
    E=2_000
    graph=random_geometric_graph(N,E)
    make_graph_connected!(graph)
    message_rate=0.1
    iterations=10_000
    warmup=1_000
    free_flow_rate=0.95
    free_flow_sampling_time=200
    initial_capacity=uniform_initial_capacity(graph,1)
    α_values=range(0.0,0.99,100)
    configs=[
        SimulationConfig(;graph,message_rate,initial_capacity,iterations,warmup,
        modifier=ModifierEdgeCapacity(;free_flow_rate,free_flow_sampling_time,momentum),
        observers=[ObserverEdgeCapacity(update_interval=free_flow_sampling_time)],
        metadata=JSON.Object("momentum"=>momentum))
        for momentum in α_values
    ]
    call_graphtraffic_rs(configs;output,overwrite)
end

function analysis(::Type{MomentumVsCapacity},
    results::AbstractDict{SimulationID,SimulationResult};
    num_threads::Integer=1)
    rows=NamedTuple[]
    for result in values(results)
        push!(rows,(
            mean_capacity=average_edge_capacity(result),
            momentum=GraphTraffic.original_json_config(result)["metadata"]["momentum"]
        ))
    end
    return DataFrames.DataFrame(rows)
end

function visualization(::Type{MomentumVsCapacity}, table::AbstractDataFrame;
    directory::AbstractString, num_threads::Integer=1)
    fig=Figure()
    ax=Axis(fig[1,1],xlabel="Momentum",ylabel="Capacidade média")
    scatter!(ax,table.momentum,table.mean_capacity)
    save(joinpath(directory, "momentum-vs-capacity.svg"), fig)
end
