#ifndef ENGINE_H
#define ENGINE_H

#include <string>
#include <vector>
#include <map>
#include <set>
#include <tuple>
#include <algorithm>
// #include "component_state.hpp"
#include "synth_state.hpp"
#include "components.hpp"

enum InOut {IO_IN, IO_OUT};
enum Types {TYPE_INT};

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

class Engine {
    public:
        /***** PUBLIC VARIABLES ******/
        // Maximum number of instructions the synthesized program may have
        int max_instrs;
        // Path relative to the synth engine executable containing a binary
        std::string path_to_binary;
        // Path relative to a CSV file containing IO examples
        std::string path_to_examples;
        // How we delimit each part of an example
        std::string example_delimiter;
        // The word we use to mark a specific example argument as output
        std::string out_delimiter;
        // The word we use to mark a specific example argument as input
        std::string in_delimiter;
        // The word we use to mark a specific example argument as an integer
        std::string int_delimiter;
        // A vector containing each example.
        // Each entry is a further vector with a 3 tuple
        // Each tuple contains <InOut, Types, Value>.
        // Outputs are stored before inputs
        std::vector<std::vector<std::tuple<int, int, uint64_t>>> examples;

        // This stores all permutations of specific instruction orderings and their
        // corresponding IO argument combinations.
        // The key represents the choice of function/component orderings we choose
        //      "0,1,2": Choode component id 0, 1, 2 in that order
        //      "2,1,15": Choose component id 2, 1, 15 in that order
        // The value represents a SynthState object for all the permutations of IO orderings between
        // these choices of compoonents and their orderings
        std::map<std::string, SynthState *> synth_state;

        /***** PUBLIC FUNCTIONS ******/
        /**
         * @brief Construct a new Engine object
         */
        Engine(std::string path_to_binary, std::string path_to_examples, int max_instrs);
        /**
         * @brief Destroy the Engine object
         */
        ~Engine();

        /**
         * @brief load_components : Loads the database of information
         * 
         * @returns bool : True if load was successful False otherwise
         */
        bool load_components();

        /**
         * @brief load_test_cases : Loads up the IO examples which we want to synthesize for
         * 
         * @return true 
         * @return false 
         */
        bool load_test_cases();

        /**
         * @brief prep_synth : Prepares a binary to be synthesized
         *  generates fuzzing information to get input output examples
         * 
         * @returns int
         *  0 : successful
         *  -1 : error (unable to find binary)
         */
        int prep_synth(std::string path_to_binary);

        /**
         * @brief synth : Synthesize a function given a set of components to use
         */
        void synth();

        /**
         * @brief verify : Verify that a synthesized function actually matches 
         *  all our input/output examples
         * @returns bool : True if verifiation succeeds else false
         */
        bool verify();

        /**
         * @brief debrittle : Generate a verified p_dash which is different 
         *  from the input p. Check that p == p_dash semantically
         */
        void debrittle();

        /**
         * @brief add_component : Add a verified component to our ground truth set
         */
        void add_component();
    
    private:
        /**
         * @brief update_examples : Updates our examples
         * 
         * @param ex 
         */
        void update_examples(std::vector<std::string> ex);

        /**
         * @brief choose_func : Chooses a function to for the id-th component we wish to
         *  add to our synthesized program
         * 
         * @param num_instr : The number of components (functions) we wish to use
         * @return int : An index into FUNC defined in components.hpp
         */
        int choose_func(int max_num_instr, int num_instr_to_choose);

        /**
         * @brief choose_arg_in : Chooses the arguments for the id-th component we wish to
         *  add to our synthesized program
         * 
         * @param id : The id-th component we are choosing arguments for
         * @return std::vector<int> : A vector of integers stating which component we wish to choose inputs from
         *  The length of this must match the comp_id used (index into FUNC).
         * 
         * TODO: Add support for constants
         */
        std::vector<int> choose_arg_in(int id, int comp_id);
};

#endif // ENGINE_H