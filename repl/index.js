import * as axios from 'axios';

const scrollToBottom = (id) => {
    const element = document.getElementById(id);
    element.scrollTop = element.scrollHeight;
};

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
	    } else if (result) {
	        addTranscript('< ' + input + '\n> ' + r.sexp_to_string(result));
	    } else {
	        addTranscript('< ' + input + '\n...');
	    }
      scrollToBottom('repl-transcript-holder');
	});
}

axios.get('clvm_tools_rs_bg.wasm', {responseType: 'blob'}).then((resp) => {
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
