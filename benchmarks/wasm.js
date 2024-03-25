const fs = require('fs');

var args = process.argv.slice(2);
if (args.length != 1) {
    console.log("Expected two args: 0: path to folder containing wasm file to run, 1: program.");
    console.log("e.g.: $ node --experimental-wasm-return_call run_wasm.js ./binaries/ vs_easy");
    process.exit(1);
}
path = args[0];
// if (path.charAt(path.length - 1) != "/") { path = path + "/" }

// program = args[1];

function write_int (value) {
    process.stdout.write(value.toString())
}

function write_char (value) {
    var chr = String.fromCharCode(value);
    process.stdout.write(chr);
}

let importObject = {
    env: {
        $write_char: write_char,
        $write_int32: write_int,
	$write_int64: write_int,
    }
};

(async () => {
    const start_startup = Date.now();
    const bytes = fs.readFileSync(path);

    const obj = await WebAssembly.instantiate(
        new Uint8Array (bytes), importObject
    );
    const stop_startup = Date.now();
    const time_startup = stop_startup - start_startup;

    try {
        const start_main = Date.now();
        obj.instance.exports.$main_function();
        const stop_main = Date.now();
        const time_main = stop_main - start_main;

        let bytes = obj.instance.exports.bytes_used.value;
        let time_pp = undefined;

        if (obj.instance.exports.result_out_of_mem.value == 1) {
            console.log("Ran out of memory.");
            process.exit(1);
        } else {
            const res_value = obj.instance.exports.result.value;
            process.stdout.write("====>");

            const start_pp = Date.now();
	    
            obj.instance.exports.$pretty_print_constructor(res_value); console.log(""); // newline
            const stop_pp = Date.now();
            time_pp = stop_pp - start_pp;
        }

        console.log(`Benchmark ${path}: {{"time_startup": "${time_startup}", "time_main": "${time_main}", "time_pp": "${time_pp}"}} (in ms)`);
    } catch (error) {
        console.log(error);
        process.exit(1);
    }
})();
