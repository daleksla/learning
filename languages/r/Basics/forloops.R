# R supports for loops
# Like C&Affiliated languages & if statements, curly brackets determine the beginning and end of statements

for (i in 1:20) #for each loop, i will hold a value between (&inc.) 1 & 20
{
  if (i %% 15 == 0) #note, if the statements of a if/for loop amount to a line, curly brackets aren't required
	  cat("FIZZBUZZ ") #note: %% represents the modulo function (aka return remainder from division)
  else if (i %% 3 == 0) 
	  cat("fizz ") 
  else if (i %% 5 == 0) 
	  cat("buzz ")
  else 
	  cat(i," ")
}