# In R, datasets presented to us that must be optimised in the way of column headers & the data each cell stores
# This allows for more effective storage, extracting and analysis
# This file is an example of scenarios of how we format tables

library(lubridate) # note: 'lubridate' is an R package that makes it easier to work with dates compared to the built in date functions
library(tidyverse)

#...in my notes (R/Tidyverse/rvest/readingWebites.R), I used the 'rvest' package to obtain a table from the internet containing American Football match statistics
#...we will be continuing from there, converting the data into a proper Tibble for clean usage and analysis

sb = sb[c(-1,-2),] # remove top two rows (it imported from the website as cells rather then column header)
names(sb) = c("number", "date", "site", "result") # assign vector of column names as the 'names' (column names) of data-frame

as_tibble(sb) %>% # re-write 'sb' as a tibble
	mutate(sb, number = 1:nrow(sb)) %>% # overwrite 'number' column with numerical values - we get the values from 1 to the amount of rows in tibble 'sb'
	sb = mutate(sb, date=mdy(date)) %>% # overwrite date column with a converted date object (rather then TEXT / String)
	sb = separate(sb,result,c("winner","loser"),sep=', ') # create two columns (one for the part prior to the separator and the latter for after) from results column, where ', '

pattern = ' \\d+$' # we can create regex patterns - in this case, the pattern is a space (' '), followed by any digit ('\\d'), following by the end symbol of a string ('+$')
sb %>%
	mutate(sb, winner_score=as.numeric(str_extract(winner,pattern))) %>% # here we extract a string which follows the given pattern, make it a number create a new column called 'winner_score'
	mutate(sb, winner=gsub(pattern, "", winner)) %>% # we then over-write the winner column by replacing substituting the parts matching the pattern with nothing / empty string ("")
	mutate(sb, loser_score=as.numeric(str_extract(loser,pattern))) %>% # here we extract a string which follows the given pattern, make it a number create a new column called 'loser_score'
	sb = mutate(sb, loser=gsub(pattern, "", loser)) # we then over-write the loser column by replacing substituting the parts matching the pattern with nothing / empty string ("")

print(sb) # this will print a clean Tibble