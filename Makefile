.PHONY: index check-index test-lean
# rebuild the results tables on the front page from conjectures/*/result.json
index:
	python3 scripts/build_index.py
check-index:
	python3 scripts/build_index.py --check
# the checker's own tests: needs ./setup.sh to have installed Lean; about 5 minutes
test-lean:
	./tests/test_lean_checker.sh
