import * as axios from 'axios';

function repl() {
	console.log('about to require clvm_tools_rs');
	var r = require('./clvm_tools_rs.js');

	var repl = r.create_repl();
	console.log('repl',repl);

	var replButton = document.getElementById('repl-send-input');

	function addTranscript(s) {
	    var replTranscript = document.getElementById('repl-transcript');
	    var lines = s.split('\n');
	    for (var i = 0; i < lines.length; i++) {
	        var line = lines[i];
	        var lineElement = document.createElement('pre');
	        lineElement.appendChild(document.createTextNode(line));
	        replTranscript.appendChild(lineElement);
	    }
	}

	replButton.addEventListener('click', () => {
	    var replInput = document.getElementById('repl-input');
	    console.log(replInput);
	    var input = replInput.value.trim();
	    console.log(input);
	    var result = r.repl_run_string(repl, input);
	    if (result.error !== undefined) {
	        addTranscript('E ' + result.error);
	    } else if (result != null) {
	        addTranscript('< ' + input + '\n> ' + r.sexp_to_string(result));
	    } else {
	        addTranscript('< ' + input + '\n...');
	    }
	});
}

axios.get('/clvm_tools_rs_bg.wasm', {responseType: 'blob'}).then((resp) => {
	if (resp.status != 200) {
		console.error(resp);
		return;
	}
	resp.data.arrayBuffer().then((buf) => {
		const imfs = new BrowserFS.FileSystem.InMemory();
		BrowserFS.initialize(imfs);
		BrowserFS.BFSRequire('fs').writeFileSync("clvm_tools_rs_bg.wasm", Buffer.from(buf));
		repl();
	});
});
/*
var replButton = document.getElementById('repl-send-input');
var replInput = document.getElementById('repl-input');
var replTranscript = document.getElementById('repl-transcript');

function addTranscript(s) {
    var lines = s.split('\n');
    for (var i = 0; i < lines.length; i++) {
        var line = lines[i];
        var lineElement = document.createElement('pre');
        lineElement.appendChild(document.createTextNode(line));
        replTranscript.appendChild(lineElement);
    }
}

replButton.addEventListener('click', () => {
    var input = replInput.value.trim();
    var result = r.repl_run_string(input);
    if (result.error !== undefined) {
        addTranscript('E ' + result.error);
    } else if (result != null) {
        addTranscript('< ' + input + '\n> ' + r.sexp_to_string(result));
    } else {
        addTranscript('< ' + input + '\n...');
    }
});
*/
