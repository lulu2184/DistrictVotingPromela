mtype = { REQUEST, GRANT, INQUIRE, RELINQUISH, RELEASE }

#define n 2
#define m 2
#define N (n * m)
#define neighborNum (m + n - 2)
#define reqLimit 1

typedef Node {
	int csTimes;			/* How many times has it requested the critical section. */
	bit inCS;				/* If it's in CS 1, otherwise 0 */
	int reqNodes[N];		/* A queue for node which has asked this node for CS access. (-1 for empty slot) */
	int reqTimestamp[N];	/* Timestamp for requests in the queue (reqNodes) */
	int vote;				/* The id of the node which it gave the vote to. (-1 if the vote is still on its hand) */
	int voteCount;			/* The number of votes it has got for its requests. */
	int neighb[neighborNum];/* Neighbors in the same district */
};

chan c[N] = [neighborNum] of {mtype, int, int};
Node nodes[N];
int currentTime = 0;

inline processRequest(nid) {

}

inline processGrant(nid, source) {
}

inline processRelease(nid, source) {
	nodes[nid].vote = -1;
	
}

inline requestCS(nid) {
	int i = 0;
	do
	::(i<len(nodes[nid])) -> d_step { c[neighb[i]]!REQUEST; i++; }
	:: else -> d_step { csTimes++; break; }
	od;
}

inline exitCS(nid) {
	int i = 0;
	do
	::(i<len(nodes[nid])) -> d_step { c[neighb[i]]!RELEASE; i++; }
	:: else -> d_step { nodes[nid].inCS = 0; nodes[nid].voteCount = 0; break; }
	od;
}

proctype Processor(int nid) {
	mtype type;
	int source;
	int ts;
	do
	:: (len(c[nid]) > 0) -> c[nid]?type(source, ts);
		if
		:: type == REQUEST -> processRequest(nid);
		:: type == GRANT -> processGrant(nid, source);
		:: type == RELEASE -> processRelease(nid, source);
		fi
	:: (nodes[nid].csTimes < reqLimit) -> requestCS(nid);
	:: (nodes[nid].inCS == 1) -> exitCS(nid);
	od;
}

init {
	int i = 0;
	do
	:: (i < N) -> run Processor(i); i++;
	:: else -> break;
	od;
}
