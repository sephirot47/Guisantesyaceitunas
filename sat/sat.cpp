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
  litToRetraClausesB = vector< vector<bool> >(numVars+1, vector<bool>(numClauses, false));

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
        else if(jval == FALSE) ++numFalses;
        else return false;
    }

   return (numFalses == 1 && numUndefs == 2); //Is it a retraclause?
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
/*
        const vector<int> &clausesToCheckForConflict = (currentValueInModel(alit) == TRUE) ?
                                                        litToClausesWhereIsNegative[alit] :
                                                        litToClausesWhereIsPositive[alit];*/
        const vector<int> &clausesToCheckForConflict = litToClauses[alit];

        //The decision is to make lit=TRUE/FALSE, so lets check for conflict in
        //the clauses where it is apporting nothing (where is negative/positive)
        //as the other ones are surely giving TRUE because of this decission
        //so there there wont be any conflict
        for(uint i = 0; i < clausesToCheckForConflict.size(); ++i)
        {
            int numUndefs = 0, numFalses = 0, numTrues = 0, lastLitUndef = 0;
            bool someLitTrue = false;
            int cc = clausesToCheckForConflict[i];

            for(uint j = 0; !someLitTrue && j < LITS_PER_CLAUSE; ++j)
            {
                const int jval = currentValueInModel(clauses[cc][j]);
                if(jval == TRUE) { ++numTrues; someLitTrue = true; }
                else if (jval == UNDEF)
                {
                    ++numUndefs;
                    lastLitUndef = clauses[cc][j];
                }
                else ++numFalses;
            }

            int lit0 = abs(clauses[cc][0]), lit1 = abs(clauses[cc][1]), lit2 = abs(clauses[cc][2]);

            //cout << litToRetraClauses[alit].size() << endl;
            bool wasRetra = litToRetraClausesB[lit0][cc] || litToRetraClausesB[lit1][cc] || litToRetraClausesB[lit2][cc];
            bool isRetra = isRetraclause(clauses[cc]);
            if(!wasRetra && isRetra)
            {
                if(lit0 != alit) ++litScores[lit0]; //increase score to the two retrapartners
                if(lit1 != alit) ++litScores[lit1]; //increase score to the two retrapartners
                if(lit2 != alit) ++litScores[lit2]; //increase score to the two retrapartners

                litToRetraClauses[alit].push_back(cc);
                litToRetraClausesB[alit][cc] = true; //retraculprit
            }


            if(wasRetra && !isRetra) // if it was retra before, but now it is not...
            {
                int litCulprit = -1; //Locate the retraculprit of its retra before, and substract score to its retrapartners
                if     (litToRetraClausesB[lit0][cc]) litCulprit = lit0;
                else if(litToRetraClausesB[lit1][cc]) litCulprit = lit1;
                else if(litToRetraClausesB[lit2][cc]) litCulprit = lit2;
                else cout << "THIS SHOULD NEVER HAPPEN!" << endl;

                if(lit0 != litCulprit) --litScores[lit0]; //decrease score to the two retrapartners
                if(lit1 != litCulprit) --litScores[lit1]; //decrease score to the two retrapartners
                if(lit2 != litCulprit) --litScores[lit2]; //decrease score to the two retrapartners

                litToRetraClausesB[litCulprit][cc] = false; //retraculprit

                //Take retraclause out of litCulprit list
                for(auto it = litToRetraClauses[litCulprit].begin(); it != litToRetraClauses[litCulprit].end(); ++it)
                {   //Take retraclause out of lit list
                    if(cc == *it)
                    {
                        litToRetraClauses[litCulprit].erase(it);
                        break;
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
    int alit = abs(lit);
    int lastLitValue = model[alit];

    //For every clause, change temporary the model value,
    // to check if its a clause which was retraclause,
    // and after the change it isnt. In case this happens,
    // substract score!
    for(int j = 0; j < litToClauses[alit].size(); ++j)
    {
        model[alit] = lastLitValue; //necessary, to undo the UNDEF change of every iteration

        int cc = litToClauses[alit][j]; //cout << "lit: " << abs(lit) << ", j: " << j << ", current clause: " << cc << endl;
        bool wasRetra = isRetraclause( clauses[cc] );

        model[alit] = UNDEF; //change, check if the change undoes retraclause in case it was

        if(wasRetra && !isRetraclause(clauses[cc]))
        {
            //Locate the culprit
            for(uint k = 0; k < LITS_PER_CLAUSE; ++k)
            {
                const int klit = abs(clauses[cc][k]);

                for(auto it = litToRetraClauses[klit].begin(); it != litToRetraClauses[klit].end(); ++it)
                {
                    if(j == *it)
                    {
                        for(uint m = 0; m < LITS_PER_CLAUSE; ++m)
                        {   //Decrease heuristic for the not two retraclause responsibles
                            if(clauses[cc][m] != klit)
                                --litScores[alit];
                        }

                        litToRetraClauses[klit].erase(it); //jlit is not a retraclause responsible anymore
                        break;
                    }
                }
            }
        }
    }

    model[alit] = UNDEF; //backtrack it
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

  int maxScore = -1;
  int maxLit = -1;
  for (uint i = 1; i <= numVars; ++i)
  {
    if(litScores[i] < 0) { cout << "LIT SCORE NEGATIVE, SHOULD ENVER HAPPEN" << endl; }

    if (currentValueInModel(i) == UNDEF &&
        litScores[i] > maxScore)
    {
      maxScore = litScores[i];
      maxLit = i;
    }
  }
  if (maxLit >= 1) return maxLit;

  //for (uint i = 1; i <= numVars; ++i) // stupid heuristic:
  //  if (model[i] == UNDEF) return i;  // returns first UNDEF var, positively
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
