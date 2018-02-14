//
//
// Generates a random planar graph.
// Outputs the complement of the random graph.
//
//
#include <iostream>
#include <set>
#include <vector>

using namespace std;

int main() {

  int n;
  cin >> n;

  vector<set<int> > adj_list;
  adj_list.resize(n);

  int top = 0;
  int bot = 1;
  adj_list[0].insert(1);
  adj_list[1].insert(0);
  for (int i=2;i<n;i++) {
      adj_list[bot].insert(i);
      adj_list[top].insert(i);
      adj_list[i].insert(top);
      adj_list[i].insert(bot);
    if ((rand()/(RAND_MAX*1.0))<0.5) {
      top=i;
            // new top = i
    } else {
      bot=i;
            // new bot = i
    }
  }
  vector<set<int> > adj_list2;
  adj_list2.resize(n);
  for (int i=0;i<n;i++) {
    for (int j=0;j<n;j++) {
      if (adj_list[i].count(j)==0) {
	adj_list2[i].insert(j);
      }
    }
  }
  
  
  cout << n << endl;
  for (int i=0;i<n;i++) {
    cout << i << " ";
    for (set<int>::iterator p=adj_list2[i].begin();
	 p!=adj_list2[i].end();++p) {
      cout << *p << " ";
    }
    cout << endl;
  }
}
