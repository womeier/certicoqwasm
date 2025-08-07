{
  lib,
  pkgs,
  mkCoqDerivation,
  coq,
  wasmcert,
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
    wasmcert
    compcert
    ExtLib
    metacoq
  ];

  patchPhase = ''
    patchShebangs ./configure.sh
    patchShebangs ./clean_extraction.sh
    patchShebangs ./make_plugin.sh
  '';

  meta = {
    description = "CertiCoq-Wasm";
    maintainers = with maintainers; [ womeier ];
    license = licenses.mit;
  };
}
