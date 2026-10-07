using GraphTraffic
using GraphTraffic.orchestrator: Experiment,
                                 run_simulation, run_analysis, run_visualization
import GraphTraffic.orchestrator: simulation, analysis, visualization
using Graphs
using DataFrames
using CairoMakie
using Random: MersenneTwister

struct BarabasiLimitedRouting <: Experiment end
seed=123456789
function balanced_comparison_configs(adaptive_configs::AbstractVector{<:SimulationConfig},
                                     results::AbstractDict{SimulationID,SimulationResult})
    [SimulationConfig(; graph=config.graph,
                      initial_capacity=balanced_initial_capacity(
                          config.graph, total_edge_capacity(results[config.id]);
                          rng=MersenneTwister(seed)),
                      routing=config.routing, message_rate=config.message_rate,
                      iterations=config.iterations, warmup=config.warmup, seed=config.seed,
                      observers=config.observers)
     for config in adaptive_configs]
end

function simulation(::Type{BarabasiLimitedRouting};
                    output::AbstractString, num_threads::Integer, overwrite::Bool)
    n = 2_000
    m = 1
    message_rate = 2e-2
    iterations = 10_000
    warmup = 1000
    capacity_modifier = ModifierEdgeCapacity(free_flow_rate=0.99, free_flow_sampling_time=100)
    capacity_observer = ObserverEdgeCapacity(update_interval=100)
    graph = barabasi_albert(n, m; complete=true, rng=MersenneTwister(2026))
    initial_capacity = balanced_initial_capacity(graph, ne(graph))
    configs = [SimulationConfig(; graph, initial_capacity, routing=LimitedVisibility(radius),
                                message_rate, iterations, warmup, seed=2026,
                                modifiers=[capacity_modifier], observers=[capacity_observer])
               for radius in 0:diameter(graph)]
    adaptive_results = call_graphtraffic_rs(configs; output, threads=num_threads, overwrite)
    comparisons = balanced_comparison_configs(configs, adaptive_results)
    call_graphtraffic_rs(comparisons; output, threads=num_threads, append=true)
    nothing
end

function analysis(::Type{BarabasiLimitedRouting},
                  results::AbstractDict{SimulationID,SimulationResult};
                  num_threads::Integer=1)
    rows = NamedTuple[]
    for result in values(results)
        routing = result.routing::LimitedVisibility
        adaptive = any(modifier -> modifier["type"] == "ModifierEdgeCapacity",
                       get(GraphTraffic.metadata(result), "modifiers", []))
        push!(rows, (; simulation_id=string(result.id), visibility=Int(routing.radius),
                     capacity_strategy=adaptive ? "adaptive" : "balanced",
                     average_traveling_time=result.average_traveling_time,
                     average_edge_capacity=average_edge_capacity(result; over=:final),
                     total_edge_capacity=total_edge_capacity(result),
                     message_rate=result.message_rate))
    end
    DataFrame(rows)
end

function visualization(::Type{BarabasiLimitedRouting},
                       table::AbstractDataFrame;
                       directory::AbstractString, num_threads::Integer=1)
    adaptive = sort(table[table.capacity_strategy .== "adaptive", :], :visibility)
    balanced = sort(table[table.capacity_strategy .== "balanced", :], :visibility)
    figure = Figure(size=(1200, 450))
    travel_axis = Axis(figure[1, 1], title="Tempo médio de viagem",
                       xlabel="Visibilidade", ylabel="Tempo médio de viagem", yscale=log10)
    lines!(travel_axis, adaptive.visibility, adaptive.average_traveling_time;
           color=:royalblue, linewidth=3, label="Adaptada")
    lines!(travel_axis, balanced.visibility, balanced.average_traveling_time;
           color=:darkorange, linewidth=3, label="Balanceada")
    axislegend(travel_axis; position=:rt)
    capacity_axis = Axis(figure[1, 2], title="Capacidade média final por aresta",
                         xlabel="Visibilidade", ylabel="Capacidade média", yscale=log10)
    lines!(capacity_axis, adaptive.visibility, adaptive.average_edge_capacity;
           color=:forestgreen, linewidth=3)
    save(joinpath(directory, "barabasi-limited-routing.svg"), figure)
    nothing
end
