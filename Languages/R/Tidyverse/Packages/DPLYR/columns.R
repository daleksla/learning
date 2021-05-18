# The R tidyverse package “dplyr” (pronounced “DEE-ply-er”) is a powerful package
# It manipulates, cleans and summarises structured data
# It makes data exploration and data manipulation easy and fast in R
# dplyr allows us to extract rows based on logical criteria and columns based on column names

library(tidyverse)
# install.packages("nycflights13") # run only once - it's just a dataset we're using
library(nycflights13)
names(flights) #display column names of dataset

# The 'select' function allows us to extract select columns from a dataset - which returns a new Tibble
# Below are 4 versions of said function you can use (where first variable is always a dataset)
select(flights, year, month, day) # the latter 3 are desired columns
select(flights, year:day) # from column year to (&inc.) column day
select(flights, -year) 
select(flights, -(year:day))

# There are certain methods / helper functions we can use with the 'select' function to make column selection easier
select(flights, starts_with("sched")) # finds a column beginning with the substring "sched"
select(flights, ends_with("delay")) # finds a column ending with the substring "delay"
select(flights, last_col()) # extracts last column of the tibble

# If we wish for a vector to be returned, which can use the 'pull()' function instead - note: the helper functions won't work!
pull(flights, sched_arr_time)

# We can modify column names (note: this will only return a modified copy, you must overwrite it manually)
rename(flights, destination=dest)

# We can add new columns to our data structures too using the 'mutate()' function!
# In the below example, we will add the columns gain & speed
newTibble = mutate(flights, gain=arr_delay-dep_delay, speed=distance/(air_time/60))
names(newTibble) # to see if the additional columns are present

# We can exclusively create new columns (ie. we create a tibble using table data and return only the new columns)
exclusiveTibble = transmute(flights, gain=arr_delay-dep_delay, gain_per_hour=gain/(air_time/60))
names(exclusiveTibble)

# Whilst Grouping doesn't change how the data looks (apart from listing how it's grouped), it changes how DPLYR functions interact
# This is achieved using the 'group_by()' function 
summarise(flights, count = n()) # this counts (general) total amount of entries
summarise(group_by(flights, year), count = n()) # by grouping the tibble by year, running the n() (a counting function) will count each year's occurance