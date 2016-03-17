#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
#include <list>
#include <map>

using namespace std;

#define LITS_PER_CLAUSE 3
#define UNDEF -1
#define TRUE 1
#define FALSE 0

typedef vector<int> Clause;

uint numVars;
uint numClauses;
vector<Clause> clauses; //{l12, l59, l3, ...} all positive

vector<int> model;      //{l0:FALSE, l1:FALSE, l2:TRUE, l3:UNDEF, l4:TRUE, l5:UNDEF, l6:FALSE, ...}
uint modelStackCurrentSize = 0;
vector<int> modelStack; //{0,3,54,6,1, 0,9,7,65,19

//For the lit i, it contains all the clauses where it appears
vector< vector<int> > litToClausesWhereIsPositive;
vector< vector<int> > litToClausesWhereIsNegative;
vector< vector<int> > litToClauses;

//<Literal, Frequency>
vector< pair<int,int> > litsOrderedByFrequencyDesc;

vector< list<int> >  litToRetraClauses; //lit to a list of index retraclauses where it is the culprit of retraclausing

//For the lit i, it contains the number of times
vector<int> litsHeuristic;

int propagations = 0;
int decisions = 0;

vector<int> litScores;

uint indexOfNextLitToPropagate;
uint decisionLevel;

void printClause(const Clause &c)
{
    cout << "clause:(";
    for (uint i = 0; i < c.size()-1; ++i)
    {
        cout << c[i] << " || ";
    }
    cout << c[c.size()-1] << ")" << endl;
}

bool sortByFreq(const pair<int,int>& left, const pair<int,int>& right)
{
    return left.second > right.second;
}

void readClauses()
{
  // Skip comments
  char c = cin.get();
  while (c == 'c')
  {
    while (c != '\n') c = cin.get();
    c = cin.get();
  }  

  //modelStack.resize(numVars * 3);

  // Read "cnf numVars numClauses"
  string aux;
  cin >> aux >> numVars >> numClauses;
  litsOrderedByFrequencyDesc.resize(numVars);
  for(uint i = 0; i < numVars; ++i)
  {
      litsOrderedByFrequencyDesc[i].first = (i+1); //lit
      litsOrderedByFrequencyDesc[i].second = 0;    //freq=0
  }

  litToClausesWhereIsPositive.resize(numVars+1);
  litToClausesWhereIsNegative.resize(numVars+1);
  litToClauses.resize(numVars+1);
  litsHeuristic.resize(numVars, 0); //freq=0
  litScores.resize(numVars+1, 0);
  litToRetraClauses  = vector< list<int> >(numVars+1, list<int>());

  clauses.resize(numClauses);

  // Read clauses
  for (uint i = 0; i < numClauses; ++i)
  {
    int lit;
    int lits[LITS_PER_CLAUSE]; int j = 0;
    while (cin >> lit && lit != 0)
    {
        clauses[i].push_back(lit);
        lits[j++] = lit;
    }

    for(uint k = 0; k < LITS_PER_CLAUSE; ++k)
    {
        lit = lits[k];

        litsOrderedByFrequencyDesc[abs(lit)].second++; //Increase frequency

        if(lit > 0) litToClausesWhereIsPositive[abs(lit)].push_back(i);
        else        litToClausesWhereIsNegative[abs(lit)].push_back(i);
        litToClauses[abs(lit)].push_back(i);
    }
  }

  std::sort(litsOrderedByFrequencyDesc.begin(),
            litsOrderedByFrequencyDesc.end(),
            sortByFreq);
}

inline int currentValueInModel(int lit)
{
    return (lit >= 0) ? model[lit] : (model[-lit] == UNDEF ? UNDEF : (1-model[-lit]));
}


void setLiteralToTrue(int lit)
{
  modelStack.push_back(lit);
  if (lit > 0)
  {
      model[lit] = TRUE;
  }
  else
  {
      model[-lit] = FALSE;
  }
}

bool isRetraclause(const Clause &clause)
{
    int numFalses = 0, numUndefs = 0;
    for(uint j = 0; j < LITS_PER_CLAUSE; ++j)
    {
        const int jval = currentValueInModel(clause[j]);
        if (jval == UNDEF) ++numUndefs;
        else ++numFalses;
    }

   return (numFalses == 1 && numUndefs == 2); //Is it a retraclause?
}

bool propagateGivesConflict()
{
    while ( indexOfNextLitToPropagate < modelStack.size() )
    {
        //Propagate last decision
        int lit = modelStack[indexOfNextLitToPropagate];
        ++indexOfNextLitToPropagate;
        ++propagations;

        const vector<int> &clausesToCheckForConflict = (currentValueInModel(abs(lit)) == TRUE) ?
                                                        litToClausesWhereIsNegative[abs(lit)] :
                                                        litToClausesWhereIsPositive[abs(lit)];

        //The decision is to make lit=TRUE/FALSE, so lets check for conflict in
        //the clauses where it is apporting nothing (where is negative/positive)
        //as the other ones are surely giving TRUE because of this decission
        //so there there wont be any conflict
        for(uint i = 0; i < clausesToCheckForConflict.size(); ++i)
        {
            int numFalses = 0;
            int numUndefs = 0;
            int lastLitUndef = 0;
            bool someLitTrue = false;
            int cc = clausesToCheckForConflict[i];

            for(uint j = 0; !someLitTrue && j < LITS_PER_CLAUSE; ++j)
            {
                const int jval = currentValueInModel(clauses[cc][j]);
                if(jval == TRUE) someLitTrue = true;
                else if (jval == UNDEF)
                {
                    ++numUndefs;
                    lastLitUndef = clauses[cc][j];
                }
                else ++numFalses;
            }

            if(isRetraclause(clauses[cc]))
            {
                //++litScores[abs(lit)];
                litToRetraClauses[abs(lit)].push_back(cc);
            }
            else
            {
                for(uint j = 0; j < LITS_PER_CLAUSE; ++j)
                {
                    const int jlit = abs(clauses[cc][j]);

                    //cout << litToRetraClauses[jlit].size() << endl;
                    for(auto it = litToRetraClauses[jlit].begin(); it != litToRetraClauses[jlit].end(); ++it)
                    {
                        if(i == *it)
                        {
                            for(uint k = 0; k < LITS_PER_CLAUSE; ++k)
                            {   //Decrease heuristic for the not two retraclause responsibles
                                if(clauses[cc][k] != jlit)
                                    --litScores[abs(lit)];
                            }

                            litToRetraClauses[jlit].erase(it); //jlit is not a retraclause responsible anymore
                            break;
                        }
                    }
                }
            }

            if (!someLitTrue) //for each clause
            {
                if(numUndefs == 0)
                {
                    //CONFLICT! All literals are false!
                    return true;
                }
                else if(numUndefs == 1)
                {
                    setLiteralToTrue(lastLitUndef);
                }
            }
        }

    }

    return false;
}


void backtrack()
{
  uint i = modelStack.size() -1;
  int lit = 0;
  while (modelStack[i] != 0) // 0 is the DL mark
  {
    lit = modelStack[i];
    int lastLitValue = model[abs(lit)];

    //For every clause, change temporary the model value,
    // to check if its a clause where it was retraclause,
    // and after the change it isnt. In case this happens,
    // substract score!
    for(int j = 0; j < litToClauses[abs(lit)].size(); ++j)
    {
        int cc = litToClauses[abs(lit)][i];
        bool wasRetraclause = isRetraclause( clauses[cc] );

        model[abs(lit)] = UNDEF; //change, check if the change undoes retraclause in case it was

        if(wasRetraclause && !isRetraclause( clauses[cc] ))
        {
            for(uint k = 0; k < LITS_PER_CLAUSE; ++k)
            {
                const int klit = abs(clauses[cc][k]);

                for(auto it = litToRetraClauses[klit].begin(); it != litToRetraClauses[klit].end(); ++it)
                {
                    if(i == *it)
                    {
                        for(uint m = 0; m < LITS_PER_CLAUSE; ++m)
                        {   //Decrease heuristic for the not two retraclause responsibles
                            if(clauses[cc][m] != klit)
                                --litScores[abs(lit)];
                        }

                        litToRetraClauses[klit].erase(it); //jlit is not a retraclause responsible anymore
                        break;
                    }
                }
            }
        }

        model[abs(lit)] = lastLitValue; //change
    }

    model[abs(lit)] = UNDEF; //change

    modelStack.pop_back();
    --i;
  }

  // at this point, lit is the last decision
  modelStack.pop_back(); // remove the DL mark
  --decisionLevel;
  indexOfNextLitToPropagate = modelStack.size();
  setLiteralToTrue(-lit);  // reverse last decision
}

int getNextDecisionLiteral()
{
  ++decisions;

  if(decisionLevel == 0)
  {
      for(uint i = 0; i < numVars; ++i)
      {
          if(currentValueInModel(litsOrderedByFrequencyDesc[i].first) == UNDEF)
              return litsOrderedByFrequencyDesc[i].first;
      }
  }

  int maxScore = 0;
  int maxLit = -1;
  for (uint i = 1; i <= numVars; ++i)
  {
    if (litScores[i] > maxScore)
    {
      maxScore = litScores[i];
      maxLit = i;
    }
  }
  if (maxLit > 0) return maxLit;

  for (uint i = 1; i <= numVars; ++i) // stupid heuristic:
    if (model[i] == UNDEF) return i;  // returns first UNDEF var, positively
  return 0; // reurns 0 when all literals are defined
}


void checkmodel()
{
  for (uint i = 0; i < numClauses; ++i)
  {
    bool someTrue = false;
    uint j;
    for (j = 0; not someTrue and j < LITS_PER_CLAUSE; ++j)
    {
      someTrue = (currentValueInModel(clauses[i][j]) == TRUE);
    }
    if (not someTrue)
    {
      cout << "Error in model, clause is not satisfied:";
      printClause(clauses[j]);
      cout << endl;
      exit(1);
    }
  }  
}

void printTimePropsAndDecisions(clock_t start)
{
    double timeTaken = ((double)(clock() - start) / CLOCKS_PER_SEC);
    cout  <<  "\tTime: " << timeTaken << "\ts" <<
              "\tDecisions: " << decisions << "   "
              "\tP/s: " << ((double) propagations) / timeTaken << endl;
}

int main()
{
  clock_t start = clock();

  readClauses(); // reads numVars, numClauses and clauses
  model.resize(numVars+1,UNDEF);
  indexOfNextLitToPropagate = 0;  
  decisionLevel = 0;

  // DPLL algorithm
  while (true)
  {
    while ( propagateGivesConflict() )
    {
      if ( decisionLevel == 0)
      {
          cout << "UNSATISFIABLE"; printTimePropsAndDecisions(start);
          return 10;
      }

      backtrack();
    }

    int decisionLit = getNextDecisionLiteral();
    if (decisionLit == 0)
    {
        checkmodel();
        cout << "SATISFIABLE"; printTimePropsAndDecisions(start);
        return 20;
    }

    // start new decision level:
    ++decisionLevel;
    ++indexOfNextLitToPropagate;
    modelStack.push_back(0);       // push mark indicating new DL
    setLiteralToTrue(decisionLit); // now push decisionLit on top of the mark
  }
}  
