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

	var replInput = document.getElementById('repl-input');
  var cm = CodeMirror.fromTextArea(replInput, {
        lineNumbers: false,
        mode: 'scheme'
  });
	var replButton = document.getElementById('repl-send-input');

  function resetInput(s) {
	    var replInput = document.getElementById('repl-input');
      if (replInput) {
          replInput.value = s;
      }
      if (cm) {
          cm.setValue(s);
      }
  }

  function addTranscript(classes, s, assign) {
	    var replTranscript = document.getElementById('repl-transcript');
	    var lineElement = document.createElement('pre');
      lineElement.setAttribute('class', classes);
	    lineElement.appendChild(document.createTextNode(s));
      if (assign) {
          var buttonElement = document.createElement('button');
          buttonElement.setAttribute('class', 'text-copy-button');
          buttonElement.addEventListener('click', () => {
              navigator.clipboard.writeText(s);
          });
          lineElement.appendChild(buttonElement);
          buttonElement = document.createElement('button');
          buttonElement.setAttribute('class', 'text-repeat-button');
          buttonElement.addEventListener('click', () => {
              resetInput(s);
          });
          lineElement.appendChild(buttonElement);
      }
	    replTranscript.appendChild(lineElement);
	}

	replButton.addEventListener('click', () => {
	    var replInput = document.getElementById('repl-input');
	    var input = cm.getValue().trim();
	    var result = r.repl_run_string(repl, input);

	    addTranscript('repl-t-input', input, true);
      if (result === null || result === undefined) {
          addTranscript('repl-t-waiting', '...');
	    } else if (result.error !== undefined) {
	        addTranscript('repl-t-error', 'E ' + result.error);
	    } else if (result) {
	        addTranscript('repl-t-output', '> ' + r.sexp_to_string(result));
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
