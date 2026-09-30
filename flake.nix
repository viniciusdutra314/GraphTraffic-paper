{
  description = "GraphTraffic paper: Julia and Rust environments";

  inputs.self.submodules = true;
  inputs.graphtraffic-jl.url = "path:./GraphTraffic-jl";

  outputs = { graphtraffic-jl, ... }: {
    inherit (graphtraffic-jl) packages devShells checks;
  };
}
