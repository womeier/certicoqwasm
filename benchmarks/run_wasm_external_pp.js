const fs = require('fs');

var args = process.argv.slice(2);

if (args.length == 0) { process.exit(1); }

binary_path = args[0];

var pp_function;

if (args.length > 1) {
    if (args[1] == "constructor") { pp_function = '$pretty_print_constructor' }
    else if (args[1] == "i63") { pp_function = '$pretty_print_i63' }
}

function write_int (value) {
    process.stdout.write(value.toString())
}

function write_char (value) {
    var chr = String.fromCharCode(value);
    process.stdout.write(chr);
}

const print_list = (val, dataView, print_elem) => {

    if (val & 1) { process.stdout.write("nil"); }
    else {
	process.stdout.write("(cons ");

	const head = dataView.getInt32(val+4, true);

	print_elem(head, dataView);

	process.stdout.write(" ");

	const tail = dataView.getInt32(val+8, true);

	print_list(tail, dataView, print_elem);

	process.stdout.write(")");
    }
}

const print_i63 = (ptr, dataView) => {

    const val = dataView.getBigUint64(ptr, true);

    process.stdout.write(val.toString());
}

let importObject = {
    env: {
        $write_char: write_char,
        $write_int: write_int,
    }
};

(async () => {
    try {
	const bytes = fs.readFileSync(binary_path);

	const obj = await WebAssembly.instantiate(
	    new Uint8Array (bytes), importObject
	);

	obj.instance.exports.$main_function();

	if (obj.instance.exports.result_out_of_mem.value == 1) {
            console.log("Ran out of memory.");
            process.exit(1);
	} else {
            const res_value = obj.instance.exports.result.value;
	    const memory = obj.instance.exports.memory;
	    const dataView = new DataView(memory.buffer);

	    // print_list(res_value, dataView, print_i63);
	    print_i63(res_value, dataView);

	    process.stdout.write("\n");
	}
    } catch (error) {
	console.log(error);
	process.exit(1);
    }})();
