using GraphTraffic
using GraphTraffic.orchestrator: Experiment,
                                 run_simulation, run_analysis, run_visualization
import GraphTraffic.orchestrator: simulation, analysis, visualization
using Graphs
using DataFrames
using CairoMakie
using Random: MersenneTwister

struct BarabasiLimitedRouting <: Experiment end

const BARABASI_PARAMETERS = (
    n=500,
    m=1,
    message_rate=0.01,
    iterations=300_000,
    warmup=30_000,
    initial_capacity_per_edge=1,
    free_flow_rate=0.999,
    free_flow_sampling_time=100,
    seed=123456789,
    # Empty means all visibilities, from zero through the graph diameter.
    visibilities=Int[],
)

generate_barabasi() = barabasi_albert(
    BARABASI_PARAMETERS.n, BARABASI_PARAMETERS.m;
    complete=true, rng=MersenneTwister(BARABASI_PARAMETERS.seed))

visibilities_to_simulate(graph) = isempty(BARABASI_PARAMETERS.visibilities) ?
    collect(0:diameter(graph)) : BARABASI_PARAMETERS.visibilities

function simulation(::Type{BarabasiLimitedRouting};
                    output::AbstractString, num_threads::Integer, overwrite::Bool)
    params = BARABASI_PARAMETERS
    capacity_modifier = ModifierEdgeCapacity(
        free_flow_rate=params.free_flow_rate,
        free_flow_sampling_time=params.free_flow_sampling_time)
    capacity_observer = ObserverEdgeCapacity(update_interval=params.free_flow_sampling_time)
    graph = generate_barabasi()
    initial_capacity = uniform_initial_capacity(graph, params.initial_capacity_per_edge)
    adaptive_configs = [SimulationConfig(; graph, initial_capacity, routing=LimitedVisibility(visibility_radius),
                                message_rate=params.message_rate,
                                iterations=params.iterations, warmup=params.warmup,
                                seed=params.seed,
                                modifiers=[capacity_modifier], observers=[capacity_observer])
               for visibility_radius in visibilities_to_simulate(graph)]
    adaptive_results = call_graphtraffic_rs(adaptive_configs; output, threads=num_threads, overwrite)

    fixed_configs = [SimulationConfig(; graph=config.graph,
                      initial_capacity=balanced_initial_capacity(
                          config.graph, total_edge_capacity(adaptive_results[config.id]);
                          rng=MersenneTwister(params.seed)),
                      routing=config.routing, message_rate=config.message_rate,
                      iterations=config.iterations, warmup=config.warmup, seed=config.seed,
                      observers=config.observers)
     for config in adaptive_configs]
    call_graphtraffic_rs(fixed_configs; output, threads=num_threads, append=true)
    nothing
end

function analysis(::Type{BarabasiLimitedRouting},
                  results::AbstractDict{SimulationID,SimulationResult};
                  num_threads::Integer=1)
    parameters = BARABASI_PARAMETERS
    graph = generate_barabasi()
    expected_by_visibility_radius = Dict{Int,Float64}()
    rows = NamedTuple[]
    for result in values(results)
        routing = result.routing::LimitedVisibility
        visibility_radius = Int(routing.radius)
        expected = get!(expected_by_visibility_radius, visibility_radius) do
            average_expected_limited_visibility_route_length(graph; visibility_radius, num_threads)
        end
        traveling_time = result.average_traveling_time
        is_adaptive = any(modifier -> modifier["type"] == "ModifierEdgeCapacity",
                       get(GraphTraffic.metadata(result), "modifiers", []))
        push!(rows, (; simulation_id=string(result.id), visibility=visibility_radius,
                     capacity_strategy=is_adaptive ? "adaptive" : "fixed",
                     travel_time_ratio=traveling_time / expected,
                     average_edge_capacity=average_edge_capacity(result; over=:final)))
    end
    DataFrame(rows)
end

function visualization(::Type{BarabasiLimitedRouting},
                       table::AbstractDataFrame;
                       directory::AbstractString, num_threads::Integer=1)
    adaptive = sort(table[table.capacity_strategy .== "adaptive", :], :visibility)
    fixed = sort(table[table.capacity_strategy .== "fixed", :], :visibility)
    figure = Figure(size=(1000, 400))
    xtics = sort(unique(vcat(adaptive.visibility, fixed.visibility)))

    time_axis = Axis(figure[1, 1]; xlabel="Visibilidade",
                     ylabel="Tempo médio / tempo teórico", yscale=log10, xticks=xtics)
    scatterlines!(time_axis, adaptive.visibility, adaptive.travel_time_ratio;
                  color=:blue, label="Adaptada")
    scatterlines!(time_axis, fixed.visibility, fixed.travel_time_ratio;
                  color=:orange, label="Fixa")
    hlines!(time_axis, [1]; color=:gray, linestyle=:dash, label="Sem atraso = 1")
    axislegend(time_axis; position=:lt)

    capacity_axis = Axis(figure[1, 2]; xlabel="Visibilidade",
                         ylabel="Capacidade média final por aresta",
                         title="Capacidade adaptada", yscale=log10, xticks=xtics)
    scatterlines!(capacity_axis, adaptive.visibility, adaptive.average_edge_capacity;
                  color=:green)
    mkpath(directory)
    save(joinpath(directory, "barabasi-limited-routing.svg"), figure)
    nothing
end
