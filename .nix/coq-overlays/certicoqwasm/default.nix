{
  lib,
  pkgs,
  mkCoqDerivation,
  coq,
  wasmcert,
  coqprime,
  compcert,
  metacoq,
  ExtLib,
  version ? null,
}:

with lib;
mkCoqDerivation {
  pname = "CertiCoq-Wasm";
  mlPlugin = true;

  inherit version;
  releaseRev = v: "v${v}";

  buildInputs = [
    pkgs.clang
  ];

  propagatedBuildInputs = [
    wasmcert # TODO: enforce 2.2.0
    coqprime
    compcert
    ExtLib
    metacoq # TODO: enforce 1.3.1+8.20
  ];

  patchPhase = ''
    patchShebangs ./configure.sh
    patchShebangs ./clean_extraction.sh
    patchShebangs ./make_plugin.sh
  '';

  configurePhase = ''
    ./configure.sh local
  '';

  buildPhase = ''
    runHook preBuild
    # DST only used in runtime/Makefile
    DST=$out/lib/coq/${coq.coq-version}/user-contrib/CertiCoq/Plugin/runtime make
    runHook postBuild
    '';

  installPhase = ''
    runHook preInstall
    # DST only used in runtime/Makefile
    DST=$out/lib/coq/${coq.coq-version}/user-contrib/CertiCoq/Plugin/runtime make install
    runHook postInstall
    '';

  meta = {
    description = "CertiCoq-Wasm";
    maintainers = with maintainers; [ womeier ];
    license = licenses.mit;
  };
}
