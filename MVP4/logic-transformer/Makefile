SHELL=/bin/csh

.PHONY: all bootstrap test lint docs demo test-categorical test-upgraded test-cech test-irreversibility test-modal test-normalizer test-pgc

all: bootstrap test docs

bootstrap:
	scripts/bootstrap.csh

test:
	scripts/test.csh

test-categorical:
	cd lt-tests && racket test-categorical-enhanced.rkt

test-categorical-analysis:
	cd lt-tests && racket test-categorical-analysis.rkt

test-categorical-all:
	cd lt-tests && racket test-categorical-enhanced.rkt

test-upgraded:
	cd lt-tests && racket test-cech-upgraded.rkt
	cd lt-tests && racket test-irreversibility-upgraded.rkt
	cd lt-tests && racket test-modal-upgraded.rkt
	cd lt-tests && racket test-normalizer-upgraded.rkt
	cd lt-tests && racket test-pgc-upgraded.rkt

test-cech:
	cd lt-tests && racket test-cech-upgraded.rkt

test-irreversibility:
	cd lt-tests && racket test-irreversibility-upgraded.rkt

test-modal:
	cd lt-tests && racket test-modal-upgraded.rkt

test-normalizer:
	cd lt-tests && racket test-normalizer-upgraded.rkt

test-pgc:
	cd lt-tests && racket test-pgc-upgraded.rkt

lint:
	scripts/lint.csh

docs:
	scripts/build-docs.csh

demo:
	scripts/demo.csh



