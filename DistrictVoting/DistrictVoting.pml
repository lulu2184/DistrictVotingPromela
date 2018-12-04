mtype = { REQUEST, GRANT, INQUIRE, RELINQUISH, RELEASE }

#define n 2
#define m 2
#define N (n * m)
#define neighborNum (m + n - 1)
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
	int earliestReqIndex;
	int reqCount;
};

chan c[N] = [neighborNum * 3] of {mtype, int, int};
Node nodes[N];
int currentTime = 0;
int numInCS = 0;
bit start = 0;
int totalCSTimes = 0;

/* ltl alwaysAtMostOneCriticalProcessor { []<>(numInCS<=1) } */

/* For loop to sum inCS field for all nodes. */
inline updateNumInCS() {
	atomic {
		numInCS = 0;
		int i;
	    for (i : 0 .. (N - 1)) {
	    	numInCS = numInCS + nodes[i].inCS;
	    }
	}
}

inline updateTotalCSTimes() {
	atomic {
		totalCSTimes = 0;
		for (i : 0 .. (N - 1)) {
			totalCSTimes = totalCSTimes + nodes[i].csTimes;
		}
	}
}

inline getEarliestRequest(nid) {
	int i = 0;
	int minTs = maxTimestamp;
	int selected = -1;
	do
	:: (i < N) ->
		if
		:: ((nodes[nid].reqNodes[i] >= 0) && (nodes[nid].reqTimestamp[i] < minTs)) ->
			minTs = nodes[nid].reqTimestamp[i];
			selected = i;
		:: else -> skip;
		fi
		i++;
	:: else -> break;
	od;
	nodes[nid].earliestReqIndex = selected;
}

inline insertRequest(nid, src, ts) {
	atomic {
		int i = 0;
		do
		:: (i < N) ->
			if
			:: (nodes[nid].reqNodes[i] < 0) ->
				nodes[nid].reqNodes[i] = src;
				nodes[nid].reqTimestamp[i] = ts;
				nodes[nid].reqCount = nodes[nid].reqCount + 1;
				break;
			:: else -> skip;
			fi
			i++;
		:: else -> break;
		od;
	}
}

inline grant(nid, ind) {
	nodes[nid].vote = nodes[nid].reqNodes[ind];
	c[nodes[nid].reqNodes[ind]]!GRANT(nid, 0);
	nodes[nid].reqNodes[ind] = -1;
	nodes[nid].reqCount = nodes[nid].reqCount - 1;
}

inline processRequest(nid, src, ts) {
	insertRequest(nid, src, ts);
}

inline tryGrant(nid) {
	atomic {
		getEarliestRequest(nid);
		if
		:: (nodes[nid].earliestReqIndex >= 0) ->
			grant(nid, nodes[nid].earliestReqIndex);
		:: else -> skip;
		fi;
	}
}

inline processGrant(nid, src) {
	atomic {
		nodes[nid].voteCount++;
		if
		:: (nodes[nid].voteCount == neighborNum) ->
			nodes[nid].inCS = 1;
			nodes[nid].voteCount = 0;
			updateNumInCS();
		:: else -> skip;
		fi;
	}
}

inline processRelease(nid, source) {
	nodes[nid].vote = -1;
}

inline requestCS(nid) {
	atomic {
		int i = 0;
		currentTime++;
		do
		:: (i<neighborNum) -> c[nodes[nid].neighb[i]]!REQUEST(nid, currentTime); i++;
		:: else -> break;
		od;
		nodes[nid].csTimes++;
		updateTotalCSTimes();
	}
}

inline exitCS(nid) {
	atomic {
		int i = 0;
		do
		:: (i<neighborNum) -> c[nodes[nid].neighb[i]]!RELEASE(nid, 0); i++;
		:: else -> break;
		od;
		nodes[nid].inCS = 0;
		nodes[nid].voteCount = 0; 
	}
}

proctype Processor(int nid) {
	start == 1;
	mtype type;
	int source;
	int ts;
	do
	:: (len(c[nid]) > 0) -> c[nid]?type(source, ts);
		if
		:: type == REQUEST -> processRequest(nid, source, ts);
		:: type == GRANT -> processGrant(nid, source);
		:: type == RELEASE -> nodes[nid].vote = -1;
		fi
	:: (nodes[nid].csTimes < reqLimit) -> requestCS(nid);
	:: (nodes[nid].inCS == 1) -> exitCS(nid); 
	:: (nodes[nid].vote == -1 && nodes[nid].reqCount > 0) -> tryGrant(nid);
	:: (totalCSTimes == N && nodes[nid].reqCount == 0 && len(c[nid]) == 0) ->
		end: skip;
	od;
}

inline setup() {
	/* init nodes */
	int i = 0;
	do
	::	(i < N) ->
		nodes[i].csTimes = 0;
		nodes[i].inCS = 0;

		int j = 0;
		do
		::	(j < N) ->
			nodes[i].reqNodes[j] = -1;
			j++;
		::	else -> break;
		od;

		nodes[i].vote = -1;
		nodes[i].voteCount = 0;
		i++;
	::	else -> break;
	od;

	/* init node neighbors */
	nodes[0].neighb[0] = 0;
	nodes[0].neighb[1] = 1;
	nodes[0].neighb[2] = 2;
	nodes[1].neighb[0] = 0;
	nodes[1].neighb[1] = 1;
	nodes[1].neighb[2] = 3;
	nodes[2].neighb[0] = 0;
	nodes[2].neighb[1] = 2;
	nodes[2].neighb[2] = 3;
	nodes[3].neighb[0] = 1;
	nodes[3].neighb[1] = 2;
	nodes[3].neighb[2] = 3;
}

init {
	atomic {
		setup();
	}

	atomic {
		int i = 0;
		do
		:: (i < N) -> run Processor(i); i++;
		:: else -> break;
		od;
		start = 1;
	}
}
