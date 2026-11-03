{
  description = "GraphTraffic paper: Julia and Rust environments";

  inputs.self.submodules = true;
  inputs.graphtraffic-rs.url = "path:./GraphTraffic-rs";
  inputs.graphtraffic-jl.url = "path:./GraphTraffic-jl";
  inputs.graphtraffic-jl.inputs.graphtraffic-rs.follows = "graphtraffic-rs";
  inputs.nixpkgs.follows = "graphtraffic-jl/nixpkgs";

  outputs = { nixpkgs, graphtraffic-jl, graphtraffic-rs, ... }: {
    packages = graphtraffic-rs.packages;
    checks = graphtraffic-rs.packages;
    devShells = nixpkgs.lib.genAttrs (builtins.attrNames graphtraffic-rs.devShells)
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in {
          default = pkgs.mkShell {
            inputsFrom = [
              graphtraffic-jl.devShells.${system}.default
              graphtraffic-rs.devShells.${system}.default
            ];
          };
        });
  };
}
