mtype = { REQUEST, GRANT, INQUIRE, RELINQUISH, RELEASE }

#define n 2
#define m 2
#define N (n * m)
#define neighborNum (m + n - 2)
#define reqLimit 1
#define maxTimestamp 10000

typedef Node {
	int csTimes;			/* How many times has it requested the critical section. */
	bit inCS;				/* If it's in CS 1, otherwise 0 */
	int reqNodes[N];		/* A queue for node which has asked this node for CS access. (-1 for empty slot) */
	int reqTimestamp[N];	/* Timestamp for requests in the queue (reqNodes) */
	int vote;				/* The id of the node which it gave the vote to. (-1 if the vote is still on its hand) */
	int voteCount;			/* The number of votes it has got for its requests. */
	int neighb[neighborNum];/* Neighbors in the same district */
	int selectedReq;
};

chan c[N] = [neighborNum] of {mtype, int, int};
Node nodes[N];
int currentTime = 0;

inline getEarliestRequest(nid) {
	int i = 0;
	int minTs = maxTimestamp;
	int selected = -1;
	do
	:: (i < N) -> 
		if
		:: (nodes[nid].reqNodes[i] >= 0 && nodes[nid].reqTimestamp[i] < minTs) ->
			minTs = nodes[nid].reqTimestamp[i];
			selected = i;
		fi
	:: else -> break;
	od;
	nodes[nid].selectedReq = selected;
}

inline processRequest(nid, src, ts) {
	d_step {
		getEarliestRequest(nid);
	}
}

inline processGrant(nid) {

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

}

proctype Processor(int nid) {
	mtype type;
	int source;
	int ts;
	do
	:: (len(c[nid]) > 0) -> c[nid]?type(source, ts);
		if
		:: type == REQUEST -> processRequest(nid);
		:: type == GRANT -> processGrant(nid);
		:: type == RELEASE -> processRelease(nid, source);
		fi
	:: (nodes[nid].csTimes < reqLimit) -> requestCS(nid);
	:: (nodes[nid].inCS == 1) -> exitCS(nid);
	od;
}

inline setup() {
	d_step {
		/* init nodes */
		int nid = 0;
		do
		::	(nid < N) -> 
			nodes[nid].csTime = 0;
			nodes[nid].inCS = 0;
			
			int i = 0;
			do
			::	(i < N) ->
				nodes[nid].reqNodes[i] = -1;
				i++;
			::	else -> break;
			od;
			
			nodes[nid].vote = -1;
			nodes[nid].voteCount = 0;
			nid++;
		::	else -> break;
		od;
	
		/* init node neighbors */
		nodes[0].neighb[0] = 1;
		nodes[0].neighb[1] = 2;
		nodes[1].neighb[0] = 0;
		nodes[1].neighb[1] = 3;
		nodes[2].neighb[0] = 0;
		nodes[2].neighb[1] = 3;
		nodes[3].neighb[0] = 1;
		nodes[3].neighb[1] = 2;
	}
}

init {
	setup();

	int i = 0;
	do
	:: (i < N) -> run Processor(i); i++;
	:: else -> break;
	od;
}
