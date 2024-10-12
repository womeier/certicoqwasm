import { print_i63, print_compare, print_bool, print_nat_sexp, print_nat_notation, print_list_sexp, print_list_notation, print_option, print_prod, print_positive_sexp, print_N_sexp, print_Z_sexp, print_compcert_byte_sexp, print_carry } from './modules/pp.js';

import { readFileSync } from 'fs';

var args = process.argv.slice(2);
if (args.length != 2) {
    console.log("Expected two args: 0: path to folder containing wasm file to run, 1: program.");
    console.log("e.g.: $ node ./js/run_wasm_external_pp.js ./ vs_easy");
    process.exit(1);
}

let path = args[0];

if (path.charAt(path.length - 1) != "/") { path = path + "/" }

const program = args[1];

let importObject = { env: {} };

const carrypattern = /(add|sub)(carry)?c/;
const boolpattern = /(eq|lt|le)b/;
const comparepattern = /compare/;
const prodpattern = /(diveucl|diveucl21|mulc)/;
var pp_fun;

if (carrypattern.test(program)) { pp_fun = (val, dataView) => print_carry(val, dataView, print_i63) }
else if (boolpattern.test(program)) { pp_fun = print_bool }
else if (comparepattern.test(program)) { pp_fun = print_compare }
else if (prodpattern.test(program)) { pp_fun = (val, dataView) => print_prod(val, dataView, print_i63, print_i63) }
else { pp_fun = print_i63 }

(async () => {
    const bytes = readFileSync(path + `compute.${program}.wasm`);

    const obj = await WebAssembly.instantiate(
        new Uint8Array (bytes), importObject
    );

    try {
        obj.instance.exports.main_function();
	let bytes = obj.instance.exports.bytes_used.value;
	const dataView = new DataView(obj.instance.exports.memory);
	const res_value = obj.instance.exports.result.value;
	pp_fun(res_value, dataView);
	process.stdout.write("\n");
    }
    catch (error) {
	console.log(error);
	process.exit(1);
    }})();
