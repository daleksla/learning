# standard compile options for the c++ executable
FLAGS = -fPIC

# the python interface through swig
PYTHONI = -I/usr/local/include/python3.8 #where Python.h is stored
PYTHONL = -Xlinker -export-dynamic

# default super-target
all: 
	g++ -fPIC -c kitty.cc -o kitty.o #create kitty.o (object code)
	#note: since we're later going to make kitty.so (a shared library), we used fPIC to give each instance of it independant memory (Position Independent Code)
	swig -c++ -python -o kitty_wrap.cxx kitty.i #use our interface file to create a cpp wrapper file (note: contains code, not executable)
	g++ $(FLAGS) $(PYTHONI) -c kitty_wrap.cxx -o kitty_wrap.o #compile our interpreted cpp wrapper file to create it's object file
	g++ $(PYTHONL) $(LIBFLAGS) -shared kitty.o kitty_wrap.o -o _kitty.so #create a shared library called _kitty.so by linking (via compilation) original object & interpreted wrapper object