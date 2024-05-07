CXX_FLAGS = -Wall -Wextra -Werror

all:
	g++ ${CXX_FLAGS} -o sat main.cpp

run: all
	./sat -l input_file

ex_unsat: all
	#./sat -l inputs_unsat/uuf50-0100.cnf
	./sat -l inputs_unsat/uuf50-0163.cnf

ex_sat: all
	#./sat -l inputs/uf20-01.cnf
	#./sat -l inputs/uf20-02.cnf
	./sat -l inputs/uf20-0106.cnf
	#./sat -l inputs/uf20-03.cnf
	#./sat -l inputs/uf20-04.cnf

unsat: all
	for f in inputs_unsat/*; do \
		./sat $$f; \
		if [[ $$? != 0 ]]; then \
			echo "Segmentation fault"; \
			echo ""; \
		fi \
	done

sat: all
	for f in inputs/*; do \
		./sat $$f; \
		if [[ $$? != 0 ]]; then \
			echo "Segmentation fault"; \
			echo ""; \
		fi \
	done

debug: all
	#gdb --args ./sat -l inputs/uf20-02.cnf
	#gdb --args ./sat -l inputs/uf20-0255.cnf
	#gdb --args ./sat -l inputs_unsat/uuf50-0100.cnf
	gdb --args ./sat -l inputs_unsat/uuf50-0163.cnf
