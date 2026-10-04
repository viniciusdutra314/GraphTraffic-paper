{
  description = "Limited-visibility routing: Lean 4 and mathlib";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/ac62194c3917d5f474c1a844b6fd6da2db95077d";

  outputs = { nixpkgs, ... }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in {
      devShells = forAllSystems (system:
        let pkgs = import nixpkgs { inherit system; };
        in {
          default = pkgs.mkShell {
            packages = with pkgs; [ elan git curl cacert zstd gnutar gzip ];
            # Nix's elan patches downloaded Linux binaries for the Nix runtime.
            # Both the selected toolchain and its state belong to this project.
            shellHook = ''
              export ELAN_HOME="$PWD/.elan"
              export MATHLIB_CACHE_DIR="$PWD/.cache/mathlib"
              export PATH="${pkgs.elan}/bin:$PATH"
              export SSL_CERT_FILE="${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
            '';
          };
        });
    };
}
