mtype = { REQUEST, GRANT, INQUIRE, RELINQUISH, RELEASE }

#define n 2
#define m 2
#define N (n * m)
#define neighborNum (m + n - 1)
#define reqLimit 1
#define maxTimestamp 10000
#define INVALID 255

typedef Node {
	bit csTimes;			/* How many times has it requested the critical section. */
	bit inCS;				/* If it's in CS 1, otherwise 0 */
	byte reqNodes[N];		/* A queue for node which has asked this node for CS access. (-1 for empty slot) */
	byte reqTimestamp[N];	/* Timestamp for requests in the queue (reqNodes) */
	byte vote;				/* The id of the node which it gave the vote to. (-1 if the vote is still on its hand) */
	byte voteTS;				/* The timestamp of the request which it gave the vote to. */
	byte voteCount;			/* The number of votes it has got for its requests. */
	byte neighb[neighborNum];/* Neighbors in the same district */
	byte earliestReqIndex;
	byte reqCount;
	byte reqTime;
	bit inquired;
	byte recVote[N];
};

chan c[N] = [neighborNum * 3] of {mtype, byte, byte};
Node nodes[N];
byte currentTime = 0;
byte numInCS = 0;
bit start = 0;
byte totalCSTimes = 0;
byte votes = 0;
byte votesInChannel[N];
byte c1;

ltl alwaysAtMostOneCriticalProcessor { []<>(numInCS<=1) }
ltl alwaysAtMostOneVote { [](start -> (votes == N)) }
ltl alwaysEventuallyAccessToCriticalSection { []<>(totalCSTimes == N*reqLimit) }
ltl EventuallyExitCriticalSectionAfterEnter { []((numInCS == 1) -> <>(numInCS == 0)) }


/* For loop to sum inCS field for all nodes. */
inline updateNumInCS() {
	atomic {
		numInCS = 0;
		byte i;
	    for (i : 0 .. (N - 1)) {
	    	numInCS = numInCS + nodes[i].inCS;
	    }
	}
}

/* For loop to sum all votes */
inline sum_votes() {
	atomic {
		votes = 0;
		byte t;
		byte j;
    	for (t : 0 .. (N-1)) {
    		/* Case 1: vote on t's hand. */
    		if
    		:: (nodes[t].vote == INVALID) -> c1 = 1;
    		:: else -> c1 = 0;
    		fi;

    		/* Case 2: vote on other's hand. */
    		for (j : 0 .. (N - 1)) {
    			c1 = c1 + nodes[j].recVote[t];
    		}

    		/* Case 3: t's vote is in channel */
    		c1 = c1 + votesInChannel[t];


    		if
    		:: (c1 == 1) -> votes = votes + 1;
    		:: else -> skip;
    		fi;
    	}
    }
}

/* For loop to update the times of entering critical section */
inline updateTotalCSTimes() {
	atomic {
		totalCSTimes = 0;
		for (i : 0 .. (N - 1)) {
			totalCSTimes = totalCSTimes + nodes[i].csTimes;
		}
	}
}

/* Find out the earliest request of given node */
inline getEarliestRequest(nid) {
	byte i = 0;
	byte minTs = maxTimestamp;
	byte selected = INVALID;
	for (i : 0 .. (N - 1)) {
		if
		:: ((nodes[nid].reqNodes[i] >= 0) && (nodes[nid].reqTimestamp[i] < minTs)) ->
			minTs = nodes[nid].reqTimestamp[i];
			selected = i;
		:: else -> skip;
		fi
	}
	nodes[nid].earliestReqIndex = selected;
}

/*when receive REQUEST, process the corresponging request recording fields*/
inline insertRequest(nid, src, ts) {
	atomic {
		byte i = 0;
		for (i : 0 .. (N - 1)) {
			if
			:: (nodes[nid].reqNodes[i] < 0) ->
				nodes[nid].reqNodes[i] = src;
				nodes[nid].reqTimestamp[i] = ts;
				nodes[nid].reqCount = nodes[nid].reqCount + 1;
				break;
			:: else -> skip;
			fi
		}
	}
}

inline grant(nid, ind) {
	nodes[nid].vote = nodes[nid].reqNodes[ind];
	c[nodes[nid].reqNodes[ind]]!GRANT(nid, 0);
	votesInChannel[nid]++;
	nodes[nid].reqNodes[ind] = INVALID;
	nodes[nid].reqCount = nodes[nid].reqCount - 1;
	nodes[nid].inquired = 0;
	sum_votes();
}

inline inquire(nid) {
	if
		:: (nodes[nid].inquired == 0) ->
			c[nodes[nid].vote]!INQUIRE(nid, 0);
			nodes[nid].inquired = 1;
			sum_votes();
		:: else -> skip;
	fi;
}

inline processRequest(nid, src, ts) {
	insertRequest(nid, src, ts);
}

/* try to grant others */
inline tryGrant(nid) {
	atomic {
		getEarliestRequest(nid);
		if
		:: (nodes[nid].reqTimestamp[nodes[nid].earliestReqIndex] < nodes[nid].voteTS) ->
			inquire(nid);
		:: (nodes[nid].earliestReqIndex >= 0) ->
			grant(nid, nodes[nid].earliestReqIndex);
		:: else -> skip;
		fi;
	}
}

inline processGrant(nid, src) {
	atomic {
		votesInChannel[src]--;
		nodes[nid].voteCount++;
		nodes[nid].recVote[src] = 1;
		if
		:: (nodes[nid].voteCount == neighborNum) ->
			nodes[nid].inCS = 1;
			nodes[nid].voteCount = 0;
			updateNumInCS();
		:: else -> skip;
		fi;
		sum_votes();
	}
}

inline processInquire(nid, src) {
	atomic {
		if
		:: (nodes[nid].inCS == 0) ->
			c[src]!RELINQUISH(nid, nodes[nid].reqTime);
			votesInChannel[src]++;
			nodes[nid].recVote[src] = 0;
			sum_votes();
		:: else -> skip;
		fi;
	}
}

inline processRelinquish(nid, src, ts) {
	atomic {
		votesInChannel[nid]--;
		insertRequest(nid, src, ts);
		nodes[nid].vote = INVALID;
		sum_votes();
	}
}

inline processRelease(nid, source) {
	atomic {
		nodes[nid].vote = INVALID;
		votesInChannel[nid]--;
		sum_votes();
	}
}

inline requestCS(nid) {
	atomic {
		int i = 0;
		currentTime++;
		for (i : 0 .. (neighborNum - 1)) {
			c[nodes[nid].neighb[i]]!REQUEST(nid, currentTime);
		}
		nodes[nid].csTimes++;
		nodes[nid].reqTime = currentTime;
		updateTotalCSTimes();
	}
}

inline exitCS(nid) {
	atomic {
		int i = 0;
		for (i : 0 .. (neighborNum - 1)) {
			c[nodes[nid].neighb[i]]!RELEASE(nid, 0);
			votesInChannel[nodes[nid].neighb[i]]++;
			nodes[nid].recVote[nodes[nid].neighb[i]] = 0;
		}
		nodes[nid].inCS = 0;
		nodes[nid].voteCount = 0;
		sum_votes();
	}
}

proctype Processor(byte nid) {
	start == 1;
	mtype type;
	byte source;
	byte ts;
	do
	:: (len(c[nid]) > 0) -> c[nid]?type(source, ts);
		if
		:: type == REQUEST -> processRequest(nid, source, ts);
		:: type == GRANT -> processGrant(nid, source);
		:: type == RELEASE -> processRelease(nid, source);
		:: type == INQUIRE -> processInquire(nid, source);
		:: type == RELINQUISH -> processRelinquish(nid, source, ts);
		fi
	:: (nodes[nid].csTimes < reqLimit) -> requestCS(nid);
	:: (nodes[nid].inCS == 1) -> exitCS(nid);
	:: (nodes[nid].vote == -1 && nodes[nid].reqCount > 0) -> tryGrant(nid);
	:: (totalCSTimes == N && nodes[nid].reqCount == 0 && len(c[nid]) == 0) ->
		end:
			do
			:: (nodes[nid].reqCount == 0) -> skip;
			od;
	od;
}

inline setup() {
	/* init nodes */
	byte i = 0;
	do
	::	(i < N) ->
		nodes[i].csTimes = 0;
		nodes[i].inCS = 0;

		byte j = 0;
		do
		::	(j < N) ->
			nodes[i].reqNodes[j] = INVALID;
			nodes[i].recVote[j] = 0;
			j++;
		::	else -> break;
		od;

		nodes[i].vote = INVALID;
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

	sum_votes();

	atomic {
		byte i = 0;
		do
		:: (i < N) -> run Processor(i); i++;
		:: else -> break;
		od;
		start = 1;
	}
}
