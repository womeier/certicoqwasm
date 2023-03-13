const fs = require('fs');
const bytes = fs.readFileSync(__dirname + '/{{file}}');

let importObject = {
    env: {
        $write_int: (value) => { process.stdout.write(value.toString()) },
        $write_char: (value) => {
            var chr = String.fromCharCode(value);
            process.stdout.write(chr);
        },
    },
/*    env: {
        import_i32: 5_000_000_000, // _ is ignored in numbers in JS and WAT
        import_f32: 123.0123456789,
        import_f64: 123.0123456789,
    } */
};

(async () => {
    const obj = await WebAssembly.instantiate(
        new Uint8Array (bytes), importObject
    );

    try {
        let res = obj.instance.exports.$main_function();
        process.stdout.write("\n====>");
        obj.instance.exports.$pretty_print_constructor(res); console.log(""); // newline

        let bytes = obj.instance.exports.$get_memory_usage_in_bytes();
        console.log(`====> used ${bytes} bytes of memory`);
    } catch (error) {
        console.log(error);
        process.exit(1);
    }
})();
