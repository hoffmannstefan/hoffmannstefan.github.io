/*
 * A (very) naive implementation of the Schreier-Sims algorithm to
 *
 * (1) compute the order,
 * (2) enumerate its elements, and
 * (3) do membership queries
 *
 * on a given permutation group.
 *
 * This implementation does not reduce the number of generators in the application
 * of Schreier's lemma. By using an appropriate reduction rule (Jerrum's or Sims filter)
 * the algorithm can be made to run in polynomial time.
 *
 * This is only for educational purposes! Also, I do not try to follow any
 * good coding standards for the sake of keeping it short. For example,
 * having member variables public (especially if they are pointers to
 * heap memory) is not a good practice for sure. Also, I noticed I am not very
 * consistent for when I use std:vector, and when I use arrays. orbit_rep** in stabilizer_chain
 * might be better implemented with vector<orbit_rep> to avoid double pointers.
 *
 * The program defines four classes:
 *
 *  permutation: to represent a single permutation.
 *  orbit_rep: represents the orbit of a given point together with
 *             a right transversal of the corresponding point stabilizer.
 *  point_stabilizer: represents a point stabilizer.
 *  stabilizer_chain: a stabilizer chain, the main data structure used
 *                    in the algorithm.
 *
 * For their usage, see the main function.
 *
 * Author: Stefan Hoffmann
 * Date:   02/11/2021
 */

#include <iostream>
#include <vector>
#include <set>
#include <algorithm>
#include <assert.h>

using namespace std;

class permutation {
  friend bool operator==(const permutation& lhs, const permutation& rhs)
  {
      if(lhs.num_points != rhs.num_points)
        return false;

      for(int i = 0; i < lhs.num_points; ++i) {
        if(lhs.images[i] != rhs.images[i])
            return false;
      }
      return true;
  }

 int  num_points;
 int* images;

public:

 // By default, if no vector or array is given, the identity transformation
 // is constructed.
 permutation(int n = 0) {
    num_points = n;
    images = new int[n];
    for(int i=0;i < n; ++i)
        images[i] = i;
 }

 // computes the product of a and b, a is evaluated first.
 permutation(const permutation& a, const permutation& b) {
    assert(a.num_points == b.num_points);
    num_points = a.get_num_points();

    images = new int[num_points];

    for(int i = 0; i < num_points; ++i) {
        set_image_of(i, b.get_image_of(a.get_image_of(i)));
    }
 }

 permutation(int n, int* im_of_points) {

    num_points = n;
    images = new int[n];
    for(int i = 0; i < n; ++i)
        images[i] = im_of_points[i];
 }

 permutation(vector<int>& v) : permutation(v.size(), v.data()) {}

 permutation get_inverse() const {
    int  n = num_points;
    int* p = new int[num_points];

    for(int i = 0; i < n; ++i) {
        p[images[i]] = i;
    }

    permutation perm(n, p);

    delete p;

    return perm;
  }

 int get_num_points() const { return num_points; }

 int get_image_of(int point) const {
   if(point < num_points) {
    return images[point];
   }
   else // throw exception?
    return -1;
 }

 void set_image_of(int point, int target) {
   if(point < num_points) {
    images[point] = target;
    // prüfen, dass noch permutation
   }
 }

 void output() const {
    for(int i = 0; i < num_points; ++i) {
        if(images[i] < 10)
            cout << " ";
        cout << images[i];
        if(i < num_points - 1)
            cout << " ";
    }
    cout << endl;
 }
};


// computes the orbit of a point together with a right transversal for the point stabilizer containing the identity element
class orbit_rep {

public:
    orbit_rep(int point, int n, const vector<permutation> generators_overgroup) : m_num_points(n), m_point(point) {
        m_rep = new permutation*[n];

        for(int i = 0; i < n; ++i)
            m_rep[i] = NULL;

        // the point itself corresponds to the identity transformation
        m_rep[point] = new permutation(n);

        orbit_rec(m_rep, point, n, generators_overgroup);
    }

    ~orbit_rep() {
        for(int i = 0; i < m_num_points; ++i)
            delete m_rep[i];
        delete[] m_rep;
    }

    int get_size() const {
        int j = 0;
        for(int i = 0; i < m_num_points; ++i) {
            if(m_rep[i] != NULL)
                ++j;
        }
        return j;
    }

    void output() const {
        cout << "orbit and right transversal for point stabilizer of: " << m_point << endl;
        for(int i = 0; i < m_num_points; ++i) {
            if(m_rep[i] != NULL) {
                cout << i << " / ";
                m_rep[i]->output();
            }
        }
    }

    // Not the best approach to realize this as a public variable. It would be better to have
    // an interface (for example, by implementing iterators), but I want to keep
    // it small.
    permutation** m_rep;
    int           m_num_points;
    int           m_point;

private:

    void orbit_rec(permutation* rep[], int current, int n, const vector<permutation>& gens) {

        vector<permutation>::const_iterator it_end = gens.end();
        for(vector<permutation>::const_iterator it = gens.begin(); it != it_end; ++it) {
            int m = it->get_image_of(current);

            if(rep[m] == NULL) {
               rep[m] = new permutation(*rep[current], *it);
               orbit_rec(rep, m, n, gens);
            }
        }
    }
};

class point_stabilizer {
    vector<permutation> m_generators;
public:
    /*
     * While computing a set of generators, a right transversal is temporarily computed.
     * In case this should be stored for later use (as in the Schreier-Sims algorithm)
     * a pointer to a pointer, which is then given a location in the heap, can be provided
     * as optional last argument. By doing so, the user must take care of freeing this memory
     * later.
     */
    point_stabilizer(int point, const vector<permutation> generators_overgroup, int n, orbit_rep** arg_rep = NULL) {
        orbit_rep* r = new orbit_rep(point, n, generators_overgroup);

        permutation** rep = r->m_rep;

        // compute a set of generators using Schreier's lemma
        for(int i=0; i < n; ++i) {
            vector<permutation>::const_iterator it_end = generators_overgroup.end();
            for(vector<permutation>::const_iterator it = generators_overgroup.begin(); it != it_end; ++it) {
                int j = it->get_image_of(i);

                if(rep[i] != NULL) {
                    assert(rep[j] != NULL);
                    permutation perm(permutation(permutation(*rep[i], *it), rep[j]->get_inverse()));
                    m_generators.push_back(perm);
                }
            }
        }
        if(arg_rep != NULL)
            *arg_rep = r;
        else
            delete r;
    }

    vector<permutation> get_generators() const {
        return m_generators;
    }
};


class stabilizer_chain {

    int          m_num_points;
    orbit_rep**  m_reps; // stores an array of pointers to right transversal for the chain of point stabilizers
public:
    stabilizer_chain(int n, const vector<permutation>& generators) : m_num_points(n) {
        m_reps = new orbit_rep*[n];

        vector<permutation> gen = generators;
        for(int i = 0; i < n; ++i) {
            point_stabilizer stab(i, gen, n, &m_reps[i]);
            gen = stab.get_generators();
        }
    }

    ~stabilizer_chain() {
       for(int i=0; i < m_num_points; ++i)
           delete m_reps[i];
       delete[] m_reps;
    }

    int order() const {
        int i = 1;
        for(int j = 0; j < m_num_points; ++j)  {
          i *= m_reps[j]->get_size();
        }
        return i;
    }

    void enumerate() const {
       vector<permutation> elements;
       enum_rec(permutation(m_num_points), 0, &elements);

       vector<permutation>::iterator ip;

       ip = unique(elements.begin(), elements.end());

       elements.resize(distance(elements.begin(), ip));

       int i = 1;
       for(ip = elements.begin(); ip != elements.end(); ++ip) {
        cout << i++ << ":\t";
        ip->output();
       }
    }

    bool membership(permutation perm) const {
        for(int i = 0; i < m_num_points; ++i) {
              for(int j = 0; j <= m_num_points; ++j) {

                if(j == m_num_points)
                    return false;
                if(m_reps[i]->m_rep[j] != NULL) {
                    permutation res(perm, m_reps[i]->m_rep[j]->get_inverse());

                    if(res.get_image_of(i) == i) {
                        perm = res;
                        break;
                    }
                }
            }
        }
        return true;
    }
private:

    void enum_rec(permutation perm, int i, vector<permutation>* elements) const {
        if(i == m_num_points) {
            elements->push_back(perm);
        }
        else {
            for(int j=0; j < m_num_points; ++j) {
                if(m_reps[i]->m_rep[j] != NULL) {
                    enum_rec(permutation(perm, m_reps[i]->m_rep[j]->get_inverse()), i + 1, elements);
                }
            }
        }
    }
};

int main()
{
    vector<permutation> gens;
    int n;

    cout << "Please enter the number of points, n = ";
    cin >> n;

    cout << "Generators are entered by giving a list of integers, where the value at position i determines the image of i." << endl;
    cout << "Example, enter '1 2 0' for the permutation that maps 0 to 1, 1 to 2 and 2 to 0 on three points." << endl;
    cout << "Note that the points are numbered from 0 to n - 1." << endl;

    int  i = 1;
    bool c = true;
    do {
        cout << endl;
        cout << "Please enter generator number " << i << " by a list of " << n << " integers." << endl;
        cout << "Enter a negative value if you do not want to input further generators." << endl;
        cout << "Input: ";
        i++;

        permutation perm(n);
        int input;
        for(int j=0;j<n;++j) {
            cin >> input;
            if(input >= 0)
                perm.set_image_of(j, input);
            else {
                c = false;
                break;
            }
        }
        gens.push_back(perm);
    } while(c);

    stabilizer_chain chain(n, gens);

    do {

        cout << "Options:" << endl;
        cout << "\t(1) Compute order of the group." << endl;
        cout << "\t(2) Enumerate the elements." << endl;
        cout << "\t(3) Do a membership query." << endl;
        cout << "\t(4) Exit." << endl << endl;

        cin >> i;

        switch(i) {
        case 1:
            cout << "Order of group: " << chain.order() << endl;
            break;
        case 2:
            cout << "Enumerate group elements:" << endl;
            chain.enumerate();
            break;
        case 3:
            permutation perm(n);
            cout << "Enter permutation on " << n << " points: ";
            int input;
            for(int j=0;j<n;++j) {
                cin >> input;
                perm.set_image_of(j, input);
            }
            cout << "Result of membership query: " << chain.membership(perm) << endl;
            break;
        }
    } while(i < 4);
    return 0;
}
