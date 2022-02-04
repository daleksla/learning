# A tibble is a data-frame with additional features
# Generally, data frames are lists made up of vectors, where vectors represent each column 
# (note: vectors only store one data-type!)

library(tidyverse) # load 'tidyverse' package

# There are TWO ways to make a tribble
# Method 1 - Create vectors storing data & combine them
name = c("Salih", "Bob", "Yusuf", "Musa", "Ibrahim") #create a vector - this will be a column
rank = c(1, 3, 2, 4, 5)
age = c(20, 16, 18, 14, 10)
weight = c(115, 65, 105, 70, 75)
family = tibble(name, rank, age, weight) # create tibble itself using 'tibble()'
# Method 2 - Type out all the table in a table style format
family = tribble( # create tibble using 'tribble()' function
	~name, ~rank, ~age, ~weight,
	"Salih", 1, 20, 115,
	"Bob", 3, 16, 65,
	"Yusuf", 2, 18, 105,
	"Musa", 4, 14, 70,
	"Ibrahim", 5, 10, 75
)

# We can extract data from a tible using R's built-in functions
nrow(family) # tells how many rows (ie data entered) in a select tibble
ncol(family) # tells how many columns (ie tibble structure) in a select tibble
colnames(family) # tells us the column names / headers in a select tibble
summary(family) # produces a result summarising the results of a model - this includes minimum, LQR, IQR & UPR, mean, median and maximum values for each column
View(family) # creates a spreadsheet (note: exports image if not using R-Studio) 

# Since a tibble is made up of vectors & lists, we can access it as so ~ below are all ways of accesing 'name' column
family[1]["name"] 
family[1, "name"]
family[, "name"] # note: empty first position means assume first index
family[1, 1]
family[1][1]
family[[1]]
family$name

# We can then use ggplot to view our data in the form of a boxplot
ggplot(data = family, mapping = aes(x=name, y=weight)) + geom_boxplot()

