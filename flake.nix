{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = (
          import nixpkgs {
            inherit system;
            config.allowUnfreePredicate =
              pkg:
              builtins.elem (pkgs.lib.getName pkg) [
                "compcert"
              ];
          }
        );

        coq = pkgs.coq_8_20;
        ocamlPkgs = coq.ocamlPackages;

        coqPkgs = pkgs.coqPackages_8_20.overrideScope (
          self: super: {
            compcert = super.compcert.override { version = "3.14"; };
            # ...
          }
        );
      in
      {
        packages.default = coqPkgs.mkCoqDerivation {
          pname = "certicoq-wasm";
          owner = "Wolfgang Meier";
          version = "0.0.1";

          src = ./.;

          isPlugin = true;

          buildInputs = [ pkgs.clang ];

          propagatedBuildInputs = with coqPkgs; [
            metacoq
            ExtLib
            equations
            compcert
            wasmcert
          ];

          meta = {
            description = "CertiCoq-Wasm";
            license = pkgs.lib.licenses.mit;
          };
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = [
            self.packages.${system}.default
            coqPkgs.vscoq-language-server
            coqPkgs.coqide
          ];

          shellHook = ''
            ORIGINAL_PS1="$PS1"
            NIX_PS1="(nix) \[$ORIGINAL_PS1\]"
            export PS1="$NIX_PS1"
          '';
        };
      }
    );
}
