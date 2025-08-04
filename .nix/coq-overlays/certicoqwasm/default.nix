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
  isPlugin = true;

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

  meta = {
    description = "CertiCoq-Wasm";
    maintainers = with maintainers; [ womeier ];
    license = licenses.mit;
  };
}
