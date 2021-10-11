# adjust for https://github.com/coq/coq/pull/13656
s/subgoal/goal/g
# newlines changed, probably due to
# https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/726
/^$/d
# lines merged due to https://github.com/coq/coq/pull/14999
/[0-9]* focused goals\?$/{N;s/\n */ /;}
