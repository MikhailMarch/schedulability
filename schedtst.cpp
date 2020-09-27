#include <iostream>
#include <map>
#include <queue>
#include <string>
#include <algorithm>
#include <cassert>
#include <chrono>
#include <stdlib.h>
#include "ts.h"

using namespace std;

struct state; 

// Main data structures
TS ts; // the task system being analyzed
int m; // n. of processors
map<state, bool> generated; // set of generated nodes of the graph 

struct state {
	TS& ts; 
	enum { ADV, ALG } pl; // player (Adversary or Algorithm)
	
	int* c; // remaining execution time
	int* t; // time to next period

	state(TS& ts_) : ts(ts_) {
		c = new int [ts.n]; 
		t = new int [ts.n]; 
		for(int i=0; i<ts.n; i++) c[i] = t[i] = 0; 
		pl = ADV; 
	}
	state(const state& s) : ts(s.ts), pl(s.pl) { 
		c = new int [ts.n]; 
		t = new int [ts.n]; 
		for(int i=0; i<ts.n; i++) {
			c[i] = s.c[i]; 
			t[i] = s.t[i]; 
		}
	}
	state& operator=(const state& s) {
		if(this != &s) {
			ts = s.ts; 
			pl = s.pl; 
			for(int i=0; i<ts.n; i++) {
				c[i] = s.c[i]; 
				t[i] = s.t[i]; 
			}
		}
		return *this; 
	}
	~state() {
		delete [] c; 
		delete [] t;
	}
	
	// Time to next deadline of a task
	inline int d(int i) const { return max(t[i] - (ts.T[i] - ts.D[i]), 0); } 

	// Equality and order predicates
	bool operator==(const state& s) const { return (pl==s.pl) && equals(c,s.c,ts.n) && equals(t,s.t,ts.n); } 

	bool equals(const int* a, const int* b, int n) const {
		for(int i=0; i<n; i++)
			if(a[i]!=b[i]) return false; 
		return true;
	}

	bool operator<(const state& s) const { 
		if(pl<s.pl) return true; 
		if(s.pl<pl) return false; 
		for(int i=0; i<ts.n; i++) {
			if(c[i]<s.c[i]) return true; 
			if(s.c[i]<c[i]) return false; 
			if(t[i]<s.t[i]) return true; 
			if(s.t[i]<t[i]) return false; 
		}
		return false; 
	}
	
	// Compute a numerical ID of the state
	int id() const {
		int x = 0, b = ts.Tmax(); 
		for(int i=0; i<ts.n; i++) {
			x += c[i]; 
			x *= b;  
			x += t[i]; 
			x *= b; 
		}
		return (pl==ADV ? 2*x+1 : 2*x); 
	}
	
	// Printing functions
	void print() const {
		cout << "s" << id() << ": P" << ((int)pl)+1 << " ";  
		for(int i=0; i<ts.n; i++) {
			cout << "c["<< i << "]: " << c[i] << " "; 
			cout << "d[" << i << "]: " << d(i) << " "; 
			cout << "t["<< i << "]: " << t[i] << " "; 
		}
		cout << endl; 
	}
	
	void printCompact() const {
		cout << (pl==ADV ? "{E" : "{S"); 
		for(int i=0; i<ts.n; i++) 
			cout << "|{" << c[i] << "|" << t[i] << "}"; 
		cout << "}"; 
	}
}; 

// Options
bool quiet = false; 
bool verbose = false; 
bool dump = false; 

void init() { }

void adversaryMove(const state& s, state& v2, int K) {
	DEBUGE(K); 
	v2.pl = state::ALG; 
	for(int i=0; i<ts.n; i++) {
		if((K & (1<<i)) && s.t[i]==0) {
			v2.c[i] = ts.C[i]; 
			v2.t[i] = ts.T[i]; 
		}
	}
#ifdef DEBUG
	v2.print();
#endif
}

bool prefer(const state&, int, int); 

bool algorithmMove(const state& s, state& v1) {
	v1.pl = state::ADV;	// Dynamic priority
	int* perm = new int [ts.n]; 

	// Sort tasks/jobs according to scheduler (see prefer() function)
	for(int i=0; i<ts.n; i++) perm[i] = i; 
	for(int i=0; i<ts.n; i++)
		for(int k=i+1; k<ts.n; k++)
			if(!prefer(s, perm[i], perm[k]))
				swap(perm[i], perm[k]); 

	// Schedule the m highest-priority ones 
	for(int i=0; i<m; i++)
		v1.c[perm[i]] = max(v1.c[perm[i]]-1,0); 
	delete [] perm; 

	for(int i=0; i<ts.n; i++) {
		// Clock tick
		v1.t[i] = max(v1.t[i]-1, 0); 
		// Check deadlines
		if(v1.d(i)==0 && v1.c[i]>0) {
			// Failure
			return false; 
		}
	}
	return true; 
}

// Example 1: Global EDF
#ifdef GEDF
#define ALGNAME "GEDF"
bool prefer(const state& s, int i, int k) {
	if(s.c[i]==0 && s.c[k]==0) return (i < k); 		// no active job from i or k -- use default ordering
	if(s.c[i]==0 || s.c[k]==0) return s.c[i] > 0; 	// only 1 active -- prefer that one
	if(s.d(i) == s.d(k)) return (i < k); 			// break ties as necessary
	return (s.d(i) < s.d(k)); 						// EDF rule
}
#endif

// Example 2: Global FP (priority ordering given by indices, index 1 == highest priority)
#ifdef GFP
#define ALGNAME "GFP with the given priorities"
bool prefer(const state& s, int i, int k) {
	if(s.c[i]==0 && s.c[k]==0) return (i < k); 		// no active job from i or k -- use default ordering
	if(s.c[i]==0 || s.c[k]==0) return s.c[i] > 0; 	// only 1 active -- prefer that one
	return (i < k); 								// FP rule (no ties are possible)
}
#endif

// Example 3: Least Laxity First
// The fact that LLF is predictable is nontrivial, see Han & Park (2006)
#ifdef LLF
#define ALGNAME "LLF"
int laxity(const state& s, int i) {
	// laxity == time to deadline - remaining WCET
	return s.d(i) - s.c[i]; 
}

bool prefer(const state& s, int i, int k) {
	if(s.c[i]==0 && s.c[k]==0) return (i < k); 		// no active job from i or k -- use default ordering
	if(s.c[i]==0 || s.c[k]==0) return s.c[i] > 0; 	// only 1 active -- prefer that one
	if(laxity(s, i) == laxity(s, k)) return i < k; 	// break ties as necessary
	return laxity(s, i) < laxity(s, k); 			// LLF rule
}
#endif

bool failureStateGenerated = false;
int counter = 1;
chrono::time_point<chrono::steady_clock> mapOperationStart, mapOperationEnd, populateStart, populateEnd;
chrono::time_point<chrono::steady_clock> commonOperationStart, commonOperationEnd;
chrono::duration<double>  mapOperationTime, commonOperationTime;

void dfs(state s){
    cerr << counter << endl;
    if(s.pl==state::ADV) {
        // V1 -> V2
        for(int K=0; K<(1<<ts.n); K++) {
            state v2 = s;
            adversaryMove(s, v2, K);
            if(dump) cout << "v" << s.id() << " -> " << "v" << v2.id() << ";" << endl;
            DEBUGE(generated[v2]);
            mapOperationStart = chrono::steady_clock::now();
            if(!generated[v2]) {
                generated[v2] = true;
                mapOperationEnd = chrono::steady_clock::now();

                commonOperationStart = chrono::steady_clock::now();
                counter++;
                commonOperationEnd = chrono::steady_clock::now();
                commonOperationTime += commonOperationEnd - commonOperationStart;

                dfs(v2);
            } else {
                mapOperationEnd = chrono::steady_clock::now();
            }
            mapOperationTime += mapOperationEnd - mapOperationStart;
        }
    }
    else if(s.pl==state::ALG) {
        // V2 -> V1
        commonOperationStart = chrono::steady_clock::now();
        state v1 = s;
        bool ok = algorithmMove(s, v1);
        if(!ok) {
            //s.failure = v1.failure = true; // unnecessary -- we stop anyway
            failureStateGenerated = true;
            if(dump) {
                cout << "v" << s.id() << " [style=filled, fillcolor=red, label=\"";
                s.printCompact();
                cout << "\"];" << endl;
            }
            if(dump) cout << "}" << endl;
            populateEnd = chrono::steady_clock::now();
            chrono::duration<double> execTime = populateEnd - populateStart;
            cerr << "Execution time: " << execTime.count() << " seconds" << endl;
            cerr << "Map operation time: " << mapOperationTime.count() << " seconds" << endl;
            cerr << "Map operation time takes " << mapOperationTime.count() / execTime.count() * 100 << "% of all time" << endl;
            cerr << counter << " states generated. " << endl;
            cerr << (failureStateGenerated ? "NOT SCHEDULABLE" : "SCHEDULABLE") << " by " << ALGNAME << "." << endl;
            exit(1);
            // Break immediately -- we are done!
        }
        if(dump) cout << "v" << s.id() << " -> " << "v" << v1.id() << ";" << endl;
        commonOperationEnd = chrono::steady_clock::now();
        commonOperationTime += commonOperationEnd - commonOperationStart;
        mapOperationStart = chrono::steady_clock::now();
        if(!generated[v1]) {
            generated[v1] = true;
            mapOperationEnd = chrono::steady_clock::now();
            counter++;
            if(ok) dfs(v1);;
        } else {
            mapOperationEnd = chrono::steady_clock::now();
        }
        mapOperationTime += mapOperationEnd - mapOperationStart;
    }
    commonOperationStart = chrono::steady_clock::now();
    if(verbose) s.print();
    if(dump) { cout << "v" << s.id() << " [label=\""; s.printCompact(); cout << "\"];" << endl; }
    commonOperationEnd = chrono::steady_clock::now();
    commonOperationTime += commonOperationEnd - commonOperationStart;
}

bool populate() {
    populateStart = chrono::steady_clock::now();

    commonOperationStart = chrono::steady_clock::now();
    state start(ts);
    commonOperationEnd = chrono::steady_clock::now();
    commonOperationTime += commonOperationEnd - commonOperationStart;

    mapOperationStart = chrono::steady_clock::now();
	generated[start] = true;
    mapOperationEnd = chrono::steady_clock::now();
    mapOperationTime += mapOperationEnd - mapOperationStart;

    dfs(start);

    populateEnd = chrono::steady_clock::now();
    chrono::duration<double> execTime = populateEnd - populateStart;
    cerr << "Execution time: " << execTime.count() << " seconds" << endl;
    cerr << "Map operation time: " << mapOperationTime.count() << " seconds" << endl;
    cerr << "Map operation time takes " << mapOperationTime.count() / execTime.count() * 100 << "% of all time" << endl;
    cerr << counter << " states generated. " << endl;
    cerr << (failureStateGenerated ? "NOT SCHEDULABLE" : "SCHEDULABLE") << " by " << ALGNAME << "." << endl;
	return failureStateGenerated; 
}

void rec(unsigned long c){
    cerr << c << endl;
    rec(++c);
}

int main(int argc, char* argv[]) {
//	if(argc>1 && string(argv[1])=="-dump") dump = true;   // dump the state graph
//    if(argc>1 && string(argv[1])=="-v") verbose = true;
//    if(argc>1 && string(argv[1])=="-q") quiet = true;
//    if(dump) cout << "digraph g {\n node [shape=record];\n " << endl;
//    init();
//    if(!quiet) cerr << "Number of processors? " << endl;
//    cin >> m;
//    ts.read(quiet);
//    return ((int)populate()==0);
rec(1);
}


