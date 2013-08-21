staload "./pats_smt_print.sats"
staload "./pats_smt_solve.sats"
staload "./pats_lintprgm.sats"

%{^
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>

int solve(char *path, char *options) {
	
	pid_t pid = fork();

	if (pid == -1) {
		printf("Fork Error!\n");
		return 0;

	} else if (pid == 0) {
		execlp(path, "cvc4", "--lang=smt2", "--incremental", "-q", "-q", options, NULL);
		printf("Exec Error!\n");
		exit(0);

	} else {
		int status;
		if (waitpid(pid, &status, 0) == -1) {
		    printf("WaitPid Error!");
		    return 0;
		} else {
    		if (WEXITSTATUS(status) == 20)
    			return -1;
    		else
    			return 0;
  		}
	}	
}

%}


extern fun solve (path: string, options: string): Ans2 = "mac#solve"


implement {a}
solve_smt {n} (ics, n) = let 
	val () = print_constraints_smt (ics, n)
in 
	solve ("cvc4", "constraint_smt.out")
end


