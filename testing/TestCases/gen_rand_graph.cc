#include <iostream>
#include <set>
#include <vector>

using namespace std;

int main() {

  int n;
  cin >> n;
  double prob=0;
  cin >> prob;
  vector<set<int> > adj_list;
  adj_list.resize(n);

  for (int i=0;i<n;i++) {
    for (int j=i+1;j<n;j++) {
      if ((rand()/(RAND_MAX*1.0))<prob) {
	// add edge.
	adj_list[i].insert(j);
	adj_list[j].insert(i);
      }
    }
  }

  cout << n << endl;
  for (int i=0;i<n;i++) {
    cout << i << " ";
    for (set<int>::iterator p=adj_list[i].begin();
	 p!=adj_list[i].end();++p) {
      cout << *p << " ";
    }
    cout << endl;
  }
}
