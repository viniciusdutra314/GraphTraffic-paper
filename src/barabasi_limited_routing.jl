using GraphTraffic
using GraphTraffic.orchestrator: Experiment,
                                 run_simulation, run_analysis, run_visualization
import GraphTraffic.orchestrator: simulation, analysis, visualization
using Graphs
using DataFrames
using CairoMakie

struct BarabasiLimitedRouting{G<:AbstractGraph} <: Experiment
    graph::G
    graph_diameter::Int
    attachment_edges::Int
    graph_seed::UInt64
    message_rate::Float64
    iterations::UInt64
    warmup::UInt64
    simulation_seed::UInt64

    function BarabasiLimitedRouting(; n_vertices::Integer=64,
                                  attachment_edges::Integer=2,
                                  graph_seed::Integer=2026,
                                  message_rate::Real=0.01,
                                  iterations::Integer=5000,
                                  warmup::Integer=500,
                                  simulation_seed::Integer=42)
        n_vertices >= 2 || throw(ArgumentError("n_vertices must be at least 2"))
        1 <= attachment_edges < n_vertices ||
            throw(ArgumentError("attachment_edges must be in [1, n_vertices)"))
        graph_seed >= 0 || throw(ArgumentError("graph_seed must be nonnegative"))

        # A complete seed graph guarantees connectivity before preferential growth.
        graph = barabasi_albert(n_vertices, attachment_edges;
                                complete=true, seed=graph_seed)
        # Reuse the simulator's validation and normalized parameter types.
        baseline = SimulationConfig(; graph, routing=LimitedVisibility(0),
                                    message_rate, iterations, warmup,
                                    seed=simulation_seed)
        new{typeof(graph)}(graph, diameter(graph), Int(attachment_edges),
                           UInt64(graph_seed), baseline.message_rate,
                           baseline.iterations, baseline.warmup, baseline.seed)
    end
end

function simulation(experiment::BarabasiLimitedRouting)
    # One graph and one simulation seed isolate visibility as the changing input.
    [SimulationConfig(; graph=experiment.graph, routing=LimitedVisibility(radius),
                      message_rate=experiment.message_rate,
                      iterations=experiment.iterations, warmup=experiment.warmup,
                      seed=experiment.simulation_seed)
     for radius in 0:experiment.graph_diameter]
end

function postprocess(experiment::BarabasiLimitedRouting, result::SimulationResult)
    # Read the radius from this result's metadata; Dict iteration order is irrelevant.
    routing = result.routing::LimitedVisibility
    (; simulation_id=string(result.id), visibility=Int(routing.radius),
       average_traveling_time=result.average_traveling_time,
       message_rate=result.message_rate, simulation_seed=result.seed,
       graph_seed=experiment.graph_seed, graph_diameter=experiment.graph_diameter)
end

# Associate each row with the routing metadata carried by its result.
function analysis(experiment::BarabasiLimitedRouting,
                  results::AbstractDict{SimulationID,SimulationResult};
                  num_threads::Integer=1)
    DataFrame([postprocess(experiment, result) for result in values(results)])
end

function visualization(experiment::BarabasiLimitedRouting,
                       table::AbstractDataFrame;
                       directory::AbstractString, num_threads::Integer=1)
    ordered = sort(table, :visibility)
    ordered.visibility == collect(0:experiment.graph_diameter) ||
        throw(ArgumentError("results must contain every visibility from zero to the diameter"))

    mkpath(directory)
    figure = Figure(size=(800, 480))
    axis = Axis(figure[1, 1],
                xlabel="Routing visibility (0: random walk; $(experiment.graph_diameter): minimal paths)",
                ylabel="Average traveling time (steps, log scale)",
                title="Barabási Limited Routing: $(nv(experiment.graph)) vertices, $(experiment.attachment_edges) attachments",
                xticks=0:experiment.graph_diameter, yscale=log10)
    scatterlines!(axis, ordered.visibility, ordered.average_traveling_time)
    save(joinpath(directory, "visibility-travel-time.svg"), figure)
    nothing
end
