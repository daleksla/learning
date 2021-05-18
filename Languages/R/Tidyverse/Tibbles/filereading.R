# Inputting data is not always ideal & importing it is typically the way to go
# One way to do this is to store data in a .csv file (or a close variant) & then read it

library(tidyverse) # again, we're usually tidyverse libraries (not standard R)
mydata = read_csv("r.csv") # reads a CSV

# There are other types of storage files (such as a .tsv file) that require different function to read it
mydata = read_tsv("r.csv")

# Other types of data-storage files / files with different delimiters etc. will require a different function to extract data from it correctly
# We can specify these factors using the 'read_delim()' function
mydata = read_delim(file = "r.csv", delim = ";")

# We can also import .csv files from the internet (such as on Github Repo's) - make sure its a raw file!
csvURL = "https://raw.githubusercontent.com/fivethirtyeight/data/master/unisex-names/unisex_names_table.csv"
webdata = read_csv(csvURL)
View(arrange(webdata, gap)) 
# the 'arrange()' function orders the rows of a data frame by the values of selected columns (where webdata is our data & gap is a column)
# the 'View()' function then displays the spreadsheet