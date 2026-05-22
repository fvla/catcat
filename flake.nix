{
  description = "catcat: a tiny concatenative language template in F* and OCaml";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      lib = nixpkgs.lib;
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = f:
        lib.genAttrs systems (system:
          let
            pkgs = import nixpkgs { inherit system; };
            ocamlPkgs = pkgs.ocamlPackages;
            ocamlDeps = with ocamlPkgs; [
              ocaml
              lsp
              dune_3
              findlib
              batteries
              pprint
              ppx_deriving
              ppx_deriving_yojson
              stdint
              yojson
              zarith
            ];
          in
          f pkgs ocamlPkgs ocamlDeps);
    in {
      devShells = forAllSystems (pkgs: _ocamlPkgs: ocamlDeps: {
        default = pkgs.mkShell {
          packages = [ pkgs.fstar pkgs.gnumake ] ++ ocamlDeps;
          shellHook = ''
            export OCAMLPATH="${pkgs.fstar}/lib/fstar''${OCAMLPATH:+:$OCAMLPATH}"
          '';
        };
      });

      packages = forAllSystems (pkgs: _ocamlPkgs: ocamlDeps: {
        default = pkgs.stdenv.mkDerivation {
          pname = "catcat";
          version = "0.1.0";
          src = self;
          nativeBuildInputs = [ pkgs.fstar pkgs.gnumake ] ++ ocamlDeps;
          dontConfigure = true;
          buildPhase = ''
            export HOME="$TMPDIR"
            export OCAMLPATH="${pkgs.fstar}/lib/fstar''${OCAMLPATH:+:$OCAMLPATH}"
            make repl
          '';
          installPhase = ''
            mkdir -p "$out/bin"
            cp _build/default/bin/main.exe "$out/bin/catcat"
          '';
        };
      });

      apps = forAllSystems (pkgs: _ocamlPkgs: _ocamlDeps: {
        default = {
          type = "app";
          program = "${self.packages.${pkgs.system}.default}/bin/catcat";
        };
      });
    };
}