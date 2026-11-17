{
  description = "catcat: a concatenative language on an effect-handler kernel, specified in Lean";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in {
      devShells = forAllSystems (pkgs: {
        # elan installs the compiler named in lean-toolchain. The nixpkgs build of elan
        # patches what it downloads, so the toolchain runs on NixOS without nix-ld.
        # node is optional: `lake test` uses it to run emitted JavaScript when it is present.
        default = pkgs.mkShell { packages = [ pkgs.elan pkgs.nodejs ]; };
      });
    };
}
