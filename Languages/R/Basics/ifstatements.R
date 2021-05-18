# If statements allow our program to execute code based on pre-determined circumstances
# Like C&Affiliates, curly brackets are required to mark the beginning and end of statements
# 'if', else if' & 'else' are the keywords used to allow if statements

if (i %% 15 == 0)
{
  cat("FIZZBUZZ ") #note: %% represents the modulo function (aka return remainder from division)
}
else if (i %% 3 == 0) 
{
	cat("fizz ") 
}
else if (i %% 5 == 0)
{
	cat("buzz ")
}
else 
{
  cat(i," ")
}