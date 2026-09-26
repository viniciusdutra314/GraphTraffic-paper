{
  description = "Julia 1.12 environment for graph traffic research";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
      forEachSystem = nixpkgs.lib.genAttrs systems;
    in
    {
      devShells = forEachSystem (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
        {
          default = pkgs.mkShell {
            packages = [ pkgs.julia_112-bin ];

            shellHook = ''
              export JULIA_PROJECT=@.
              julia --startup-file=no --project=. -e 'using Pkg; Pkg.instantiate()' || exit $?
            '';
          };
        });
    };
}
