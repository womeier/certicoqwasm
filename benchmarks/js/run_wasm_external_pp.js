import { print_i63, print_compare, print_bool, print_nat_sexp, print_nat_notation, print_list_sexp, print_list_notation } from './modules/pp.js';

const test_primitives_pp_map = {
    "addition": print_nat_notation,
    "addition_primitive": print_i63
};

import { readFileSync } from 'fs';

var args = process.argv.slice(2);

if (args.length == 0) { process.exit(1); }

const binary_path = args[0];

var pp_func = null;

if (args.length > 1) {
    pp_func = test_primitives_pp_map[args[1]];
}

function write_int (value) {
    process.stdout.write(value.toString())
}

function write_char (value) {
    var chr = String.fromCharCode(value);
    process.stdout.write(chr);
}

let importObject = {
    env: {
        write_char: write_char,
        write_int: write_int,
    }
};

(async () => {
    try {
	const bytes = readFileSync(binary_path);

	const obj = await WebAssembly.instantiate(
	    new Uint8Array (bytes), importObject
	);

	const start_time = performance.now();
	obj.instance.exports.main_function();
	const stop_time = performance.now();

	const run_time = performance.now();

	if (obj.instance.exports.result_out_of_mem.value == 1) {
            console.log("Ran out of memory.");
            process.exit(1);
	} else {
            const res_value = obj.instance.exports.result.value;
	    const memory = obj.instance.exports.memory;
	    const dataView = new DataView(memory.buffer);

	    if (pp_func) {
		try {
		    console.log(`Result of running binary ${binary_path}:`);
		    pp_func(res_value, dataView);
		}
		catch (_error) {
		    console.log(`Failed to pretty print result for binary ${binary_path}`);
		}
	    }

	    process.stdout.write("\n");
	    console.log(`run time: ${run_time} ms`);
	}
    } catch (error) {
	console.log(error);
	process.exit(1);
    }})();
