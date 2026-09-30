using GraphTraffic
using GraphTraffic.orchestrator: Experiment,
                                 run_simulation, run_analysis, run_visualization
import GraphTraffic.orchestrator: simulation, analysis, visualization
using Graphs
using DataFrames
using CairoMakie

struct BarabasiLimitedRouting <: Experiment end

function simulation(::Type{BarabasiLimitedRouting})
    n = 2_000
    m = 2
    message_rate = 1e-2
    iterations = 10_000
    warmup = 1000
    capacity_modifier = ModifierEdgeCapacity(free_flow_rate=0.99, free_flow_sampling_time=100)
    capacity_observer = ObserverEdgeCapacity(update_interval=100)
    graph = barabasi_albert(n, m;complete=true)
    [SimulationConfig(; graph, routing=LimitedVisibility(radius),
                      message_rate, iterations, warmup, 
                      modifiers=[capacity_modifier], observers=[capacity_observer])
     for radius in 0:diameter(graph)]
end

function analysis(::Type{BarabasiLimitedRouting},
                  results::AbstractDict{SimulationID,SimulationResult};
                  num_threads::Integer=1)
    rows = NamedTuple[]
    for result in values(results)
        routing = result.routing::LimitedVisibility
        push!(rows, (; simulation_id=string(result.id), visibility=Int(routing.radius),
                     average_traveling_time=result.average_traveling_time,
                     average_edge_capacity=average_edge_capacity(result; over=:final),
                     message_rate=result.message_rate))
    end
    DataFrame(rows)
end

function visualization(::Type{BarabasiLimitedRouting},
                       table::AbstractDataFrame;
                       directory::AbstractString, num_threads::Integer=1)
    df = sort(table, :visibility)
    figure = Figure(size=(1000, 400))
    travel_axis = Axis(figure[1, 1], xlabel="Visibilidade",
                       ylabel="Tempo médio de viagem", yscale=log10)
    capacity_axis = Axis(figure[1, 2], xlabel="Visibilidade",
                         ylabel="Capacidade média por aresta",
                         yscale=log10)
    scatterlines!(travel_axis, df.visibility, df.average_traveling_time)
    scatterlines!(capacity_axis, df.visibility, df.average_edge_capacity)
    save(joinpath(directory, "barabasi-limited-routing.svg"), figure)
    nothing
end
