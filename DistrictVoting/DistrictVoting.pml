mtype = { REQUEST, GRANT, INQUIRE, RELINQUISH, RELEASE }

#define n 2
#define m 2
#define N (n * m)
#define reqLimit 1

chan c[N] = [m + n - 2] of {mtype, int, int};
int csTimes[N];
bit inCS[N];

inline processRequest(pid) {

}

inline processGrant(pid) {

}

inline processRelease(pid) {

}

inline requestCS(pid) {

}

inline exitCS(pid) {

}

proctype Processor(int pid, ) {
	mtype type;
	do
	:: (len(c[pid]) > 0) -> c[pid]?type(x, ts);
		if
		:: type == REQUEST -> processRequest(pid);
		:: type == GRANT -> processGrant(pid);
		:: type == RELEASE -> processRelease(pid);
		fi
	:: (csTimes[pid] < reqLimit) -> requestCS(pid);
	:: (inCS[pid] == 1) -> exitCS(pid);
	od
}

init {
	int i = 0;
	do
	:: (i < N) -> run Processor(i); i++;
	:: (i >= N) -> break;
	od
}
