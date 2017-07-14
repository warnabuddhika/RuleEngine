//
// Copyright 2012 Hakan Kjellerstrand
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

using System;
using System.Collections;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using Google.OrTools.ConstraintSolver;
using System.Collections.Generic;


public class Crew
{

    /**
     *
     * Crew allocation problem  in Google CP Solver.
     *
     * From Gecode example crew
     * examples/crew.cc
     * """
     * Example: Airline crew allocation
     *
     * Assign 20 flight attendants to 10 flights. Each flight needs a certain
     * number of cabin crew, and they have to speak certain languages.
     * Every cabin crew member has two flights off after an attended flight.
     * """
     *
     * Also see http://www.hakank.org/or-tools/crew.pl
     *
     */
    private static void Solve(int sols = 1, int minimize = 0)
    {
        Solver solver = new Solver("Crew");

        //
        // Data
        //
        string[] names = {"Tom",
                      "David",
                      "Jeremy",
                      "Ron",
                      "Joe",
                      "Bill",
                      "Fred",
                      "Bob",
                      "Mario",
                      "Ed",
                      "Carol",
                      "Janet",
                      "Tracy",
                      "Marilyn",
                      "Carolyn",
                      "Cathy",
                      "Inez",
                      "Jean",
                      "Heather",
                      "Juliet"};

        int num_persons = names.Length;


        //
        // Attributes of the crew
        //
        int[,] attributes = {
      // steward, hostess, french, spanish, german, other duties done in hours(per week)
      {1,0,0,0,1,1},   // Tom     = 0
      {1,0,0,0,0,2},   // David   = 1
      {1,0,0,0,1,0},   // Jeremy  = 2
      {1,0,0,0,0,1},   // Ron     = 3
      {1,0,0,1,0,1},   // Joe     = 4
      {1,0,1,1,0,0},   // Bill    = 5
      {1,0,0,1,0,1},   // Fred    = 6
      {1,0,0,0,0,2},   // Bob     = 7
      {1,0,0,1,1,1},   // Mario   = 8
      {1,0,0,0,0,1},   // Ed      = 9
      {0,1,0,0,0,9},   // Carol   = 10
      {0,1,0,0,0,1},   // Janet   = 11
      {0,1,0,0,0,2},   // Tracy   = 12
      {0,1,0,1,1,0},   // Marilyn = 13
      {0,1,0,0,0,1},   // Carolyn = 14
      {0,1,0,0,0,1},   // Cathy   = 15
      {0,1,1,1,1,1},   // Inez    = 16
      {0,1,1,0,0,2},   // Jean    = 17
      {0,1,0,1,1,1},   // Heather = 18
      {0,1,1,0,0,1}    // Juliet  = 19
    };


        //
        // Required number of crew members.
        //
        // The columns are in the following order:
        // staff     : Overall number of cabin crew needed
        // stewards  : How many stewards are required
        // hostesses : How many hostesses are required
        // french    : How many French speaking employees are required
        // spanish   : How many Spanish speaking employees are required
        // german    : How many German speaking employees are required
        // duration(flight)  : How long is the flight 
        // isNight   : Is night flight
        int[,] required_crew = {
        {4,1,1,1,1,1,8,1}, //0 Flight 1
        {5,1,1,1,1,1,5,1}, //1 Flight 2
        {5,1,1,1,1,1,2,1}, //2 ..
        {6,2,2,1,1,1,6,1}, //3
        {7,3,3,1,1,1,5,1}, //4
        {4,1,1,1,1,1,1,0}, //5
        {5,1,1,1,1,1,6,0}, //6
        {6,1,1,1,1,1,5,0}, //7
        {6,2,2,1,1,1,6,0}, //8 ...
        {7,3,3,1,1,1,10,0} //9 Flight 10
        };

        int num_flights = required_crew.GetLength(0);


        //
        // Decision variables
        //
        IntVar[,] crew = solver.MakeIntVarMatrix(num_flights, num_persons,
                                                 0, 1, "crew");
        IntVar[] crew_flat = crew.Flatten();

        // number of working persons
        // The MakeIntVar(i, j, name) method is a factory method that creates an integer variable whose domain is [i,j] = {i,i+1,...,j−1,j}
        //and has a name name. It returns a pointer to an IntVar
        IntVar num_working = solver.MakeIntVar(1, num_persons, "num_working"); // 1..20

        //
        // Constraints
        //

        // number of working persons
        IntVar[] nw = new IntVar[num_persons];
        for (int p = 0; p < num_persons; p++)
        {
            IntVar[] tmp = new IntVar[num_flights];
            for (int f = 0; f < num_flights; f++)
            {
                tmp[f] = crew[f, p];
            }
            nw[p] = tmp.Sum() > 0;
        }
        solver.Add(nw.Sum() == num_working);

        for (int f = 0; f < num_flights; f++)
        {
            // size of crew
            IntVar[] tmp = new IntVar[num_persons];
            for (int p = 0; p < num_persons; p++)
            {
                tmp[p] = crew[f, p];
            }
            solver.Add(tmp.Sum() == required_crew[f, 0]);

            // attributes and requirements
            for (int a = 0; a < 5; a++)
            {
                IntVar[] tmp2 = new IntVar[num_persons];
                for (int p = 0; p < num_persons; p++)
                {
                    tmp2[p] = (crew[f, p] * attributes[p, a]).Var();
                }
                solver.Add(tmp2.Sum() >= required_crew[f, a + 1]);
            }
        }

        // after a flight, break for at least two flights
        //for(int f = 0; f < num_flights - 2; f++) {
        //  for(int i = 0; i < num_persons; i++) {
        //    solver.Add(crew[f,i] + crew[f+1,i] + crew[f+2,i] <= 1);
        //  }
        //}

        // extra contraint: all must work at least two of the flights
        /*
        for(int p = 0; p < num_persons; p++) {
          IntVar[] tmp = new IntVar[num_flights];
          for(int f = 0; f < num_flights; f++) {
            tmp[f] = crew[f,p];
          }
          solver.Add(tmp.Sum() >= 2);
        }
        */


        // all memebers should only work less than 30 hours in flight
        for (int p = 0; p < num_persons; p++)
        {
            IntVar[] tmp3 = new IntVar[num_flights];
            for (int f = 0; f < num_flights; f++)
            {
                tmp3[f] = (crew[f, p] * required_crew[f, 6]).Var();
            }

            solver.Add(tmp3.Sum() <= 30);
        }

        ///Maximum Duty time per 1 week  
        //for (int p = 0; p < num_persons; p++)
        //{
        //    IntVar[] tmp4 = new IntVar[num_flights];
        //    for (int f = 0; f < num_flights; f++)
        //    {
        //        tmp4[f] = ((crew[f, p] * required_crew[f, 6]) + attributes[p, 5]).Var();
        //    }

        //    solver.Add(tmp4.Sum() <= 40);
        //}

        //assignment should not exceed maximum consecutive night duties of 2
        for (int f = 0; f < num_flights - 2; f++)
        {
            for (int i = 0; i < num_persons; i++)
            {
                solver.Add((crew[f, i] * required_crew[f, 7]) + (crew[f + 1, i] * required_crew[f, 7]) + (crew[f + 2, i] * required_crew[f, 7]) <= 2);
                //solver.Add((crew[f, i] * required_crew[f, 7]) + (crew[f + 1, i] * required_crew[f, 7])  <= 1);

            }
        }


        //
        // Search
        //
        DecisionBuilder db = solver.MakePhase(crew_flat,
                                              Solver.CHOOSE_FIRST_UNBOUND,
                                              Solver.ASSIGN_MIN_VALUE);

        if (minimize > 0)
        {
            OptimizeVar obj = num_working.Minimize(1);
            solver.NewSearch(db, obj);
        }
        else
        {
            solver.NewSearch(db);
        }

        int num_solutions = 0;
        while (solver.NextSolution())
        {
            num_solutions++;
            Console.WriteLine("Solution #{0}", num_solutions);
            Console.WriteLine("Number working: {0}", num_working.Value());


            //IList<Flight> FlightSchedule = new List<Flight>();
            for (int f = 0; f < num_flights; f++)
            {
                //Flight flight = new Flight();  

                for (int p = 0; p < num_persons; p++)
                {
                    Console.Write(crew[f, p].Value() + " ");



                }
                Console.WriteLine();
            }
            Console.WriteLine("\nFlights: ");
            for (int f = 0; f < num_flights; f++)
            {
                Console.Write("Flight #{0}: ", f);
                for (int p = 0; p < num_persons; p++)
                {
                    if (crew[f, p].Value() == 1)
                    {
                        Console.Write(names[p] + " ");
                    }
                }
                Console.WriteLine();
            }

            Console.WriteLine("\nCrew:");
            for (int p = 0; p < num_persons; p++)
            {
                Console.Write("{0,-10}", names[p]);
                for (int f = 0; f < num_flights; f++)
                {
                    if (crew[f, p].Value() == 1)
                    {
                        Console.Write(f + " ");
                    }
                }
                Console.WriteLine();
            }

            Console.WriteLine();

            if (num_solutions >= sols)
            {
                break;
            }

        }

        Console.WriteLine("\nSolutions: {0}", solver.Solutions());
        Console.WriteLine("WallTime: {0}ms", solver.WallTime());
        Console.WriteLine("Failures: {0}", solver.Failures());
        Console.WriteLine("Branches: {0} ", solver.Branches());

        solver.EndSearch();

    }


    public static void Main(String[] args)
    {
        int n = 1;
        int min = 0; // > 0 -> minimize num_working
        if (args.Length > 0)
        {
            n = Convert.ToInt32(args[0]);
        }

        if (args.Length > 1)
        {
            min = Convert.ToInt32(args[1]);
        }

        Solve(n, min);
        Console.ReadLine();
    }
}

//Maximum consecutive night duties 
//Maximum duty time for regular night duties  
//Maximum Duty time per 1 week       
