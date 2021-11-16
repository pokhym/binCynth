#ifndef UTIL_H
#define UTIL_H

#include <algorithm>
#include <vector>

// https://stackoverflow.com/questions/5095407/all-combinations-of-k-elements-out-of-n
template <typename Iterator>
inline bool next_combination(const Iterator first, Iterator k, const Iterator last)
{
   /* Credits: Thomas Draper */
   if ((first == last) || (first == k) || (last == k))
      return false;
   Iterator itr1 = first;
   Iterator itr2 = last;
   ++itr1;
   if (last == itr1)
      return false;
   itr1 = last;
   --itr1;
   itr1 = k;
   --itr2;
   while (first != itr1)
   {
      if (*--itr1 < *itr2)
      {
         Iterator j = k;
         while (!(*itr1 < *j)) ++j;
         std::iter_swap(itr1,j);
         ++itr1;
         ++j;
         itr2 = k;
         std::rotate(itr1,j,last);
         while (last != j)
         {
            ++j;
            ++itr2;
         }
         std::rotate(k,itr2,last);
         return true;
      }
   }
   std::rotate(first,k,last);
   return false;
}

inline std::vector<std::vector<int>> nCk(int n, int k) {
    std::vector<std::vector<int>> ret;
    std::vector<int> ints;
    for (int i = 0; i < n; ints.push_back(i++));

    do
    {
        std::vector<int> curr;
        for (int i = 0; i < k; ++i){
            // std::cout << ints[i];
            curr.push_back(ints[i]);
        }
        ret.push_back(curr);
    }
    while(next_combination(ints.begin(),ints.begin() + k,ints.end()));
    return ret;
}

#endif // UTIL_H