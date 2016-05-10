/**
 * Usage:
 *
 * sortcensus <mode> <levels> <input-dir> <output-dir>
 *
 * mode is either -i (invariants) or -p (Pachner moves)
 * levels is an integer, stating how many invariants to add/how many levels of
 * the Pachner graph to explore
 * <input-dir> is a directory containing .sigs files, each of which will be
 * processed
 * <output-dir> should already exist, and is where each output file will be
 * placed.
 *
 * Each file (input or output) will be as follows:
 * [invariant string]
 * <list of signatures of triangulations, all connected via Pachner moves>
 * ...
 * [queue of signatures which have not been analysed for Pachner moves]
 *
 * Note that both the invariant string and queue are optional, and that there
 * may be more than one space-separated list of signatures. The invariant
 * string, if present, beings with a hash (#) then a space, and contains
 * invariants common to all triangulations in the file. The invariants used are, in order:
 * orientability (denoted as orbl or nor)
 * homology
 * TuraevViro(3, true)
 * TuraevViro(3, false)
 * TuraevViro(4, true)
 * TuraevViro(5, true)
 * TuraevViro(5, false)
 * TuraevViro(6, true)
 * ...
 * and so on. The invariants are separated by semi-colons (;) and, if an
 * invariant string is present, it will always end with a semi-colon.
 *
 * The queue begins with #q and is a space-separated list of signatures of
 * triangulations that have yet to be analysed for Pachner moves. It is assumed
 * that every signature not in this list has been analyed. Additionally, this
 * list may contain signatures not present in the rest of the file (these
 * should be ignored).
 */

#include <dirent.h>
#include <sys/types.h>
#include <sys/stat.h>

#include <cstring>
#include <map>
#include <queue>
#include <fstream>
#include <triangulation/ntriangulation.h>

#include "threadpool.h"

using namespace regina;

struct Data {
    std::string sig;
    Data* parent;
    long depth;
    long smallest;
    Data* minimal;

    Data(const std::string& from) : sig(from), parent(0), depth(0), minimal(this) {
        smallest = sig[0] - 'a';
    }

    Data* root() {
        Data *r = this;
        while (r->parent)
            r = r->parent;
        return r;
    }
};

class Profile {
    public:
        std::string str;
        Profile(const std::string& s) : str(s) {
        }

        Profile(const Profile& other) : str(other.str) {
        }

        void extend(const NTriangulation& tri) {
            int currently_known = 0;
            size_t s = 0;
            // Find number of occurances of ; in string representation so far
            while ( (s = str.find(";",s)) != std::string::npos) {
                s+=1; // Move past the found location
                currently_known++;
            }
            switch (currently_known) {
                case 0: {
                    bool orbl = tri.isOrientable();
                    str += orbl ? "orbl" : "nor";
                    break;
                        }
                case 1:
                        {
                    str += tri.homology().str();
                    break;
                        }
                default:
                        {
                    int a = currently_known % 3;
                    int b = currently_known / 3;
                    std::stringstream s;
                    if ( a == 0 )
                        s << tri.turaevViro(2*b+1,false);
                    else if ( a == 1 )
                        s << tri.turaevViro(2*b+2,true);
                    else // a == 2 {
                        s << tri.turaevViro(2*b+3,true);
                    str += s.str();;
                        }
            }
            str += ";";
        }


        bool operator == (const Profile& rhs) const {
            return str == rhs.str;
        }

        bool operator < (const Profile& rhs) const {
            return str < rhs.str;
        }

};

std::ostream& operator << (std::ostream& out, const Profile p) {
    return out << p.str;
}

typedef std::map<std::string, Data*> Graph; // For union-find.
typedef std::map<Profile, std::vector<std::string>> Cases;
typedef std::queue<Graph::iterator> gQueue;

Data* root(Data* n) {
    Data* ans = n;
    while (ans->parent)
        ans = ans->parent;
    // Compress the tree.
    if (n == ans)
        return ans;
    Data* tmp;
    while (n->parent != ans) {
        tmp = n->parent;
        n->parent = ans;
        n = tmp;
    }
    return ans;
}

// Return value is true iff we joined two distinct components.
bool join(Data* a, Data* b) {
    Data* aRoot = root(a);
    Data* bRoot = root(b);
    if (aRoot == bRoot)
        return false;


    if (aRoot->depth > bRoot->depth) {
        bRoot->parent = aRoot;
        if (bRoot->smallest < aRoot->smallest) {
            aRoot->smallest = bRoot->smallest;
            aRoot->minimal = bRoot->minimal;
        }
    } else if (bRoot->depth > aRoot->depth) {
        aRoot->parent = bRoot;
        if (aRoot->smallest < bRoot->smallest) {
            bRoot->smallest = aRoot->smallest;
            bRoot->minimal = aRoot->minimal;
        }
    }
    else {
        aRoot->parent = bRoot;
        ++bRoot->depth;
        if (aRoot->smallest < bRoot->smallest) {
            bRoot->smallest = aRoot->smallest;
            bRoot->minimal = aRoot->minimal;
        }
    }
    return true;
}


// Reads input
int read(std::string infile, Cases& waiting, std::map<Profile, Graph>& graphs,
        std::map<Profile, unsigned>& nComp) {
    int maxN = 0;
    std::string line;
    std::ifstream inf(infile);
    Profile p("#");
    while ( std::getline(inf, line) ) {
        std::stringstream l(line);
        if (l.str()[0] == '#' && l.str()[1] != 'q') {
            p = Profile(l.str());
            continue;
        }
        std::string s;
        l >> s;
        if (s.empty())
            continue;

        // If we find #q, everything after this is things waiting to be
        // processed (rather than "everything")
        if (s == "#q") {
            while (l >> s) {
                if (! s.empty()) {
                    auto it = waiting.find(p);
                    if (it == waiting.end())
                        it = waiting.insert(std::make_pair(p, std::vector<std::string>())).first;
                    it->second.push_back(s);
                }
            }
            continue;
        }

        if (s[0] - 'a' > maxN)
            maxN = s[0] - 'a';

        NTriangulation *tri = NTriangulation::fromIsoSig(s);
        bool simple = tri->intelligentSimplify();
        delete tri;
        if (simple) {
            continue;
        }
        Data *d = new Data(s);
        auto it = graphs.find(p);
        if (it == graphs.end())
            it = graphs.insert(std::make_pair(p, std::map<std::string, Data*>())).first;
        it->second.insert(std::make_pair(s, d));

        while ( l >> s ) {
            if (! s.empty()) {
                Data *e = new Data(s);
                join(d,e);
                it->second.insert(std::make_pair(s,e));
            }
        }
        auto it2 = nComp.find(p);
        if (it2 == nComp.end())
            it2 = nComp.insert(std::make_pair(p, 0)).first;
        ++(it2->second);
    }
    return maxN;
}

void free_graphs(std::map<Profile, Graph> & graphs) {
    for( auto git = graphs.begin(); git != graphs.end(); ++git) {
        Graph & g = git->second;
        for ( auto it = g.begin(); it != g.end(); ++it) {
            // Delete Data structure
            delete it->second;
        }
    }
}

bool process(Data* p, Graph& graph, const Profile& prof, int maxN, gQueue &q,
        std::map<Profile, unsigned> nComp) {
    NTriangulation* t = NTriangulation::fromIsoSig(p->sig);
    if (t == 0)
        return true;

    size_t i;
    int j;
    std::string next;
    Graph::iterator pos;
    int smallest;
    bool shrunk = false;

    for (i = 0; i < t->countEdges(); ++i)
        if (t->threeTwoMove(t->edge(i), true, false)) {
            NTriangulation alt(*t);
            alt.threeTwoMove(alt.edge(i), false, true);
            alt.intelligentSimplify();
            next = alt.isoSig();
            smallest = next[0] - 'a';
            if (smallest < maxN)
                shrunk = true;
            pos = graph.find(next);
            if (pos == graph.end()) {
                pos = graph.insert(Graph::value_type(next, new Data(next))).first;
                q.push(pos);
                if (! join(p, pos->second)) {
                    std::cerr << "ERROR: adjacency problem!" << std::endl;
                }
            } else {
                if (join(p, pos->second))
                    --nComp[prof];
            }
        }

    for (i = 0; i < t->countEdges(); ++i)
        for (j = 0; j < 2; ++j)
            if (t->fourFourMove(t->edge(i), j, true, false)) {
                NTriangulation alt(*t);
                alt.fourFourMove(alt.edge(i), j, false, true);
                alt.intelligentSimplify();
                next = alt.isoSig();
                smallest = next[0] - 'a';
                if (smallest < maxN)
                    shrunk = true;
                pos = graph.find(next);
                if (pos == graph.end()) {
                    pos = graph.insert(Graph::value_type(next, new Data(next))).first;
                    q.push(pos);
                    if (! join(p, pos->second)) {
                        std::cerr << "ERROR: adjacency problem!" << std::endl;
                    }
                } else {
                    if (join(p, pos->second))
                        --nComp[prof];
                }
            }

    for (i = 0; i < t->countTriangles(); ++i)
        if (t->twoThreeMove(t->triangle(i), true, false)) {
            NTriangulation alt(*t);
            alt.twoThreeMove(alt.triangle(i), false, true);

            next = alt.isoSig();
            smallest = next[0] - 'a';
            if (smallest < maxN)
                shrunk = true;
            pos = graph.find(next);
            if (pos == graph.end()) {
                pos = graph.insert(Graph::value_type(next, new Data(next))).first;
                q.push(pos);
                if (! join(p, pos->second)) {
                    std::cerr << "ERROR: adjacency problem!" << std::endl;
                }
            } else {
                if (join(p, pos->second))
                    --nComp[prof];
            }
        }

    delete t;

    // Stop when we have 1 component left in the Pachner graph, and we've
    // shrunk things
    if (shrunk && (nComp[prof] == 1))
        return false;

    return true;
}

void dump_pachner(const std::string fname, const Profile& p, const Graph&
        graph, int maxN, gQueue &q) {
    typedef std::multimap<std::string, std::string> Comb;
    Comb comps;

    for (auto i = graph.begin(); i != graph.end(); ++i) {
        // Ignore bigger triangulations/signatures
        if (i->first[0] > 'a' + maxN)
            continue;
        // If the smallest representation has less than maxN tetrahedra, we
        // won't print any of the triangulations
        if (root(i->second)->smallest == maxN)
            comps.insert(std::make_pair(root(i->second)->sig, i->first));
    }

    Comb::iterator pos = comps.begin();
    Comb::iterator prev = comps.end();
    std::ofstream out(fname);
    out << p << std::endl;
    while (pos != comps.end()) {
        if (prev == comps.end() || prev->first != pos->first) {
            // New component.
            if (pos != comps.begin())
                out << '\n';
        } else {
            // Same component as the previous triangulation.
            out << ' ';
        }
        out << pos->second;

        prev = pos;
        ++pos;
    }
//    if (! q.empty()) {
//        out << std::endl << "#q";
//        do {
//            if (q.front() != graph.end())
//                out << " " << q.front()->first;
//            q.pop();
//        } while (! q.empty());
//    }
    out << std::endl;
    out.close();
}

void pachner(const std::string iname, int levels, const std::string oname) {
    Cases waiting;
    std::map<Profile, Graph> graphs;
    std::map<Profile, unsigned> nComp;
    int maxN = read(iname, waiting, graphs, nComp);
    for (auto graphit = graphs.begin(); graphit != graphs.end(); ++graphit) {
        gQueue q;
        Graph& g = graphit->second;
        bool keepGoing = true;

        // Find out if we know what should be in the queue
        auto wait = waiting.find(graphit->first);
        if (wait == waiting.end())
        // If we don't know what should be in the queue, we will add everything
            for(auto it = g.begin(); it != g.end(); ++it) {
                q.push(it);
            }
        else {
        // We know what to add, so only add those specific sigs to the queue
            for (auto sig: wait->second) {
                auto pos = g.find(sig);
                // Note that we skip sigs that we don't find in this graph
                // This means we don't have to filter the queue when
                // partitioning based on invariants.
                if (pos != g.end()) {
                    q.push(pos);
                }
            }
        }
        for (int i = 0; i < levels && keepGoing; ++i) {
            if (q.empty()) {
                std::cerr << "NOTHING REMAINING!" << std::endl;
            }
            q.push(g.end());
            while (q.front() != g.end() && keepGoing) {
                keepGoing = process(q.front()->second, g, graphit->first, maxN,
                        q, nComp);
                q.pop();
            }
            q.pop(); // pop off g.end() if it's there. If not, keepGoing is
                     // false, which means we've shrunk this component and
                     // won't ever care about the queue again
        }
        dump_pachner(oname, graphit->first, g, maxN, q);
    }
    free_graphs(graphs);
    return;
}

void dump_partition(const std::string fname, const Graph& graph, const
        std::map<std::string, Profile>& profiles, const
        std::vector<std::string> q) {

    // vector of sigs in a component
    typedef std::vector<std::string> Comp;

    // lookup root sig, gives vector of sigs in this component
    std::map<std::string, Comp> comps;

    // lookup a profile, gives vector of components with given profile
    typedef std::map<std::string, std::vector<Comp>> Part;
    Part parts;

    for (auto i = graph.begin(); i != graph.end(); ++i) {
        // We print out everything (even bigger triangulations), as we may
        // extend this graph later.
        Data *r = i->second->root();
        auto it = comps.find(r->sig);
        if (it == comps.end())
            it = comps.insert(std::make_pair(r->sig, Comp())).first;
        it->second.push_back(i->second->sig);
    }

    for (auto i = comps.begin(); i != comps.end(); ++i) {
        const Profile &p = profiles.at(i->first);
        auto it = parts.find(p.str);
        if (it == parts.end()) {
            it = parts.insert(std::make_pair(p.str,
                        std::vector<std::vector<std::string>>())).first;
        }
        it->second.push_back(i->second);
    }
    int count = 0;
    for (auto cit = parts.begin(); cit != parts.end(); ++cit) {
        std::stringstream name;
        name << fname << count++ << ".sigs";
        std::ofstream out(name.str());
        out << cit->first << std::endl;
        for (auto comp: cit->second) {
            for (auto sig: comp)
                out << sig << " ";
            out << std::endl;
        }
        // dump the whole queue (even bits that might not be in
        // this partition).
        if (q.size() > 0) {
            out << "#q";
            for (auto sig : q) {
                out << " " << sig;
            }
            out << std::endl;
        }
        // Now close file
        out.close();
    }
}

void partition(const std::string iname, int depth, const std::string oname) {
    Cases waiting;
    std::map<Profile, Graph> graphs;
    std::map<Profile, unsigned> nComp;
    read(iname, waiting, graphs, nComp);
    std::map<std::string, Profile> profiles;
    for (auto graphit = graphs.begin(); graphit != graphs.end(); ++graphit) {
        Graph& g = graphit->second;
        if (nComp[graphit->first] == 1)
            continue;
        for (auto git = g.begin(); git != g.end(); ++git) {
            Data *r = git->second->root();
            auto pit = profiles.find(r->sig);
            if (pit == profiles.end()) {
                Profile p(graphit->first);
                NTriangulation *tri = NTriangulation::fromIsoSig(r->sig);
                for(int i=0; i < depth; ++i) {
                    p.extend(*tri);
                }
                profiles.insert(std::make_pair(r->sig, p));
                delete tri;
            }
        }
        std::vector<std::string> q=waiting[graphit->first];
        dump_partition(oname, g, profiles, q);
    }
    free_graphs(graphs);
    return;
}

void usage(char* name) {
    std::cout << "Usage: " << name << " -p|-i <depth> <indir> <outdir>" << std::endl;
    std::cout << "  -p means build <depth> levels of the Pachner graph" << std::endl;
    std::cout << "  -i means add <depth> invariants to each profile" << std::endl;
    std::cout << "  <indir> must be a directory containing .sigs files" << std::endl;
    std::exit(-1);
}

extern errno;

int main(int argc, char* argv[]) {

    ThreadPool p(3); // TODO num threads
    if (argc < 4)
        usage(argv[0]);

    enum modes { PACHNER, PARTITION};
    modes mode;

    if (strncmp(argv[1], "-i", 2) == 0) {
        mode = PARTITION;
    } else if (strncmp(argv[1], "-p", 2) == 0) {
        mode = PACHNER;
    } else
        usage(argv[0]);

    int level = atoi(argv[2]);
    DIR *d = opendir(argv[4]);
    if (d == NULL) {
        if (errno == ENOENT) {
            // Set creation mask
            umask(0);
            // Create dir
            mkdir(argv[4],0755);
        } else {
        std::cerr << "Error: Could not open " << argv[3]
            << " as output directory." << std::endl;
        std::exit(1);
        }
    }
    closedir(d);

    d = opendir(argv[3]);
    if (d == NULL) {
        std::cerr << "Error: Could not open " << argv[3]
            << " as input directory." << std::endl;
        std::exit(1);
    }
    dirent *dirp;

    while (( dirp = readdir(d)) != NULL) {
        int len = strlen(dirp->d_name);
        if (len > 5) {
            if (strncmp( dirp->d_name + (len-5), ".sigs", 5) == 0) {
                std::stringstream iname;
                std::stringstream oname;
                iname << argv[3] << "/" << dirp->d_name;
                oname << argv[4] << "/";
                if (mode == PARTITION) {
                    std::string dname(dirp->d_name);
                    oname << dname.substr(0, dname.length() - 5) << "_";
                    p.enqueue(&partition, iname.str(), level, oname.str());
                } else if (mode == PACHNER) {
                    oname << dirp->d_name;
                    p.enqueue(&pachner, iname.str(), level, oname.str());
                }
            }
        }
    }
    closedir(d);

    return 0;
}

// vim: ts=4:sw=4
