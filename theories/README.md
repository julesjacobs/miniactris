This is an archived artifact for the paper [Dependent Session Protocols in Separation Logic from First Principles](https://apndx.org/pub/mpy9/miniactris.pdf)
by Jules Jacobs, Jonas Kastberg Hinrichsen, and Robbert Krebbers.
The most recent version of the Coq code is available at [https://github.com/julesjacobs/miniactris](https://github.com/julesjacobs/miniactris).


This artifact website is bidirectionally hyperlinked with the [PDF of the paper](https://apndx.org/pub/mpy9/miniactris.pdf):

* Definitions, theorems, and examples in the Coq code are hyperlinked to the corresponding location in the paper.
* Definitions, theorems, and examples in the paper are hyperlinked to the corresponding location in the Coq code.


The artifact contains the following files:

* base.v: one-shot channels without subprotocols
* sub.v: one-shot channels with subprotocols
* session.v: multi-shot session channels
* imp.v: imperative channels
* sym_close.v: symmetric close operation
* send_close.v: combined send_close operation