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

vector< vector<bool> >  litToRetraClausesB; //lit to a list of index retraclauses where it is the culprit of retraclausing
vector< list<int> >  litToRetraClauses; //lit to a list of index retraclauses where it is the culprit of retraclausing

//For the lit i, it contains the number of times
vector<int> litsHeuristic;
vector<bool> retraclauses;

int propagations = 0;
int decisions = 0;

vector<int> litScores;

uint indexOfNextLitToPropagate;
uint decisionLevel;

inline int currentValueInModel(int lit);

void printClause(const Clause &c)
{/*
    cout << "clause:(";
    for (uint i = 0; i < c.size()-1; ++i)
    {
        cout << c[i] << " || ";
    }
    cout << c[c.size()-1] << ")" << endl;
    */
    cout << "c (";
    for (uint i = 0; i < c.size()-1; ++i)
    {
        cout << currentValueInModel(c[i]) << " || ";
    }
    cout << currentValueInModel(c[c.size()-1]) << ")" << endl;
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
  litToClausesWhereIsPositive.resize(numVars+1);
  litToClausesWhereIsNegative.resize(numVars+1);
  litToClauses.resize(numVars+1);

  litsOrderedByFrequencyDesc = vector< pair<int,int> >(numVars+1, pair<int,int>(0,0));
  for(uint i = 1; i <= numVars; ++i)
  {
      litsOrderedByFrequencyDesc[i].first = i;  //lit
      litsOrderedByFrequencyDesc[i].second = 0; //freq=0
  }

  litToClausesWhereIsPositive.resize(numVars+1);
  litToClausesWhereIsNegative.resize(numVars+1);
  litToClauses.resize(numVars+1);
  litsHeuristic.resize(numVars, 0); //freq=0

  litScores.resize(numVars+1, 0);
  litToRetraClauses  = vector< list<int> >(numVars+1, list<int>());
  litToRetraClausesB = vector< vector<bool> >(numVars+1, vector<bool>(numClauses, false));

  retraclauses = vector<bool>(numClauses, false);
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

        if(lit > 0) litToClausesWhereIsPositive[lit].push_back(i);
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

inline bool isRetraclause(int i)
{
    uint countFalse = 0, countUndef = 0;
    for (uint j = 0; j < LITS_PER_CLAUSE; ++j)
    {
      const int v = currentValueInModel(clauses[i][j]);
      if (v == FALSE) ++countFalse;
      else if (v == UNDEF) ++countUndef;
      else return false;
    }

    return countFalse == 1; //return (countFalse == 1 && countUndef == 2);
}

bool propagateGivesConflict()
{
    while ( indexOfNextLitToPropagate < modelStack.size() )
    {
        //Propagate last decision
        int lit = modelStack[indexOfNextLitToPropagate];
        int alit = abs(lit);
        ++indexOfNextLitToPropagate;
        ++propagations;

        const vector<int> &clausesToCheckForConflict = litToClauses[abs(lit)]   ;
        const uint S = clausesToCheckForConflict.size();
        for(uint i = 0; i < S; ++i)
        {
            int numUndefs = 0, numFalses = 0;
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

            retraclauses[cc] = (numFalses == 1 && numUndefs == 2);

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
    int alit = abs(lit);
    model[alit] = UNDEF; //backtrack it

    const uint S = litToClauses[alit].size();
    for(uint ci = 0; ci < S; ++ci)
    {
        int cc = litToClauses[alit][ci];

        retraclauses[cc] = isRetraclause(cc);
    }

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

  int clausesChecked = 0;
  vector<int> litScores(numVars+1,0);

  for(uint i = 0; i < numClauses; ++i)
  {
    if(!retraclauses[i]) continue;
    for (uint j = 0; j < LITS_PER_CLAUSE; ++j)
    {
        const int lit = clauses[i][j];
        if (currentValueInModel(lit) == UNDEF)
            ++litScores[abs(lit)];
    }
  }

  int maxLit = -1, maxScore = 0;
  for (uint i = 1; i <= numVars; ++i)
  {
    if (litScores[i] > maxScore)
    {
      maxScore = litScores[i];
      maxLit = i;
    }
  }

  if(maxLit <= 0)
  {
      for(uint i = 1; i < numVars+1; ++i)
      {
          if(currentValueInModel(litsOrderedByFrequencyDesc[i].first) == UNDEF)
              return litsOrderedByFrequencyDesc[i].first;
      }
  }
  return maxLit;
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

    //cout << decisionLit << endl;
    //cout << "decision: " << decisionLit << endl;
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
