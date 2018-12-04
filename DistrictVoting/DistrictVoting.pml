mtype = { REQUEST, GRANT, INQUIRE, RELINQUISH, RELEASE }

#define n 2
#define m 2
#define N (n * m)
#define reqLimit 1

chan c[N] = [m + n - 2] of {mtype, int, int};
int csTimes[N];
bit inCS[N];

inline processRequest(nid) {

}

inline processGrant(nid) {

}

inline processRelease(nid) {

}

inline requestCS(nid) {

}

inline exitCS(nid) {

}

proctype Processor(int nid) {
	mtype type;
	int x;
	int ts;
	do
	:: (len(c[nid]) > 0) -> c[nid]?type(x, ts);
		if
		:: type == REQUEST -> processRequest(nid);
		:: type == GRANT -> processGrant(nid);
		:: type == RELEASE -> processRelease(nid);
		fi
	:: (csTimes[nid] < reqLimit) -> requestCS(nid);
	:: (inCS[nid] == 1) -> exitCS(nid);
	od;
}

init {
	int i = 0;
	do
	:: (i < N) -> run Processor(i); i++;
	:: (i >= N) -> break;
	od;
}
