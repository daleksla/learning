# R is very useful for data visualisation
# The function 'ggplot()' is very useful to achieve this goal
# It takes two parameters:
	# data / <param#1> ~ dataset
	# mapping / <param#2> ~ aesthetic mapping for our axis (using the 'aes()' function)
# Note: other functions are needed alongside 'ggplot()' to become useful - these are called 'geomtric objects'

library(tidyverse) #load tidyverse library
library(datasets) # get built-in datasets
data(iris) # get specific dataset
library(GGally) # library extension of 'ggplot2' - contains templates for advanced & different plots

ggplot(data = iris, mapping = aes(x=Species, y=Petal.Length)) #pass iris dataset & set axis'
# Note: the above is useless on it's own - we need to 'add' functions to be able to use the object 'ggplot()' creates
ggplot(data = iris, mapping = aes(x=Species, y=Petal.Length)) + geom_boxplot() # plot as boxplot (shows min, max, ranges)
ggplot(data = iris, mapping = aes(x=Species, y=Petal.Length)) + geom_point() # plot as scatter point graph
ggplot(data = iris, mapping = aes(x=Species, y=Petal.Length)) + geom_histogram(color="darkblue", fill="lightblue")
ggplot(data = iris, mapping = aes(x = Petal.Length)) + geom_histogram(color="blue", fill="lightblue") # plot a variable as histogram with specific aesthetics

# Note: we can generically write a plot but then add 'facet_wrap(~<category>)' to create a multi-panel of said plots split by said category
ggplot(data = titanic, aes(x=Gender)) + geom_bar(aes(fill=Survived)) + facet_wrap(~Pclass) # 3 passanger class', therefore 3 bar charts showing which Men and women survived for a certain class

#Note: we can 'flip' the axis we've set (via the aes() function) using the 'coord_flip()' function
ggplot(data = iris, mapping = aes(x=Species, y=Petal.Length)) + geom_boxplot() + coord_flip()

# note: scale_x_<scale-type> / scale_y_<scale-type> are used to aesthetically set the scales of our graphs
ggplot(data = iris, mapping = aes(x=Species, y=Petal.Length)) + geom_boxplot() + scale_x_log10() 

# You can also use 'ggplot()' to plot two vectors directly, without having to specify a dataset for it to index
# Note: you will have to set data to 'NULL', making the variable redundant
Species = pull(iris, Species)
petalLength = pull(iris, Petal.Length)
ggplot(data = NULL, mapping = aes(x=Species, y=petalLength)) + geom_boxplot()

# It is good practise to add your own captions to your plots such as titles, axis names, etc.
ggplot(data = iris, mapping = aes(x=Species, y=Petal.Length)) + geom_boxplot() + labs(title="Species vs Petal Length ",x = "Species",y = "Petal Length (cm)")

# 'ggscatmat()' function makes a scatterplot matrix for quantitative variables with density plots
# it automatically provides a scatterplot and a correlation coefficient, together with a smoothed histogram for each variable
ggscatmat(creditTibble) 
