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
        coqPackages = pkgs.coqPackages_8_20;
        compcert = coqPackages.compcert.override { version = "3.14"; };

        ocamlPackages = coq.ocamlPackages;
        vscoq-lang-server = coqPackages.vscoq-language-server;
      in
      {
        packages.default = coqPackages.mkCoqDerivation {
          pname = "certicoq-wasm";
          owner = "Wolfgang Meier";
          version = "0.0.1";

          src = ./.;

          propagatedBuildInputs =
            with coqPackages;
            [
              wasmcert
              metacoq
              ExtLib
              equations
              coqide
            ]
            ++ [
              vscoq-lang-server
              compcert
            ];

          meta = {
            description = "CertiCoq-Wasm";
            license = coqPackages.lib.licenses.mit;
          };
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = [ self.packages.${system}.default ];

          shellHook = ''
            ORIGINAL_PS1="$PS1"
            NIX_PS1="(nix) \[$ORIGINAL_PS1\]"
            export PS1="$NIX_PS1"
          '';
        };
      }
    );
}
