sc2-build-order
===============
* main.cpp  - the main solver. Accepts very general files which describe init state, exchange rules, inequalities and goal state. It is not tied to SC in any way
* sc2game.cpp - a converter of *.scspec files to *.spec files, that is converts hi-level rules of starcraft to general game rules accepted by main.cpp
* slabocator.hpp - some naive memory allocator (still better than default one)
* sc2.scspec - a simple fragment of SC2 build rules
