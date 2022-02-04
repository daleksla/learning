# Creating a line of best fit allows us to go on to predict the value of one variable given the value of another
# Linear Regression is a fancy word for finding the best possible straight line through a scatterplot relating two quantitative variables
  # In others words, its a way of calculating the line of best fit between two axis with numbers
  # Line of best fit equation for LR: y = a + bx, where a = intercept && b is slope /aka/ rise over run
# Multiple regression is finding a line of best fit considering multiple variables
  # Line of best fit equation for MR with 3 predicting variables: z = a + bx + cy
# A residual is the (vertical) distance between a data point and the regression line we calculate
  # Then, do the Residual equation: residual = y - (a + bx)
  # Note: we can use a formula to calculate b where it'll help to result in the smallest residual value, use the following formula:
    # 𝑏 = ∑( (𝑥𝑖−𝑥̅) * (𝑦𝑖 − 𝑦̅) ) / ∑( (𝑥𝑖 −𝑥̅ ) ^ 2)
    # ie. for_all_elements(element of x - mean(x)) * (element of y - mean(y)) / for_all_elements((element of x - mean(x)) * 2)
# 'lm()' is an R function that can do all both LR and MR for us
	# It can calculate a, b, etc. values
	# We provide it the resultant values followed by our 'causing factor'
		# usage e.g lm(weight~calorieintake)
	# In reality you should use that (especially when there are 3+ predicting factors)
# We can calculate how efficient a regression model is by using the 'coefficient of determination'
  # Ths is also known as 'R squared' or 'Multiple R-squared'
  # It is the (correlation between the original and predicted value) ^ 2
	  # The higher it is, the more efficient the model is
  # We can also use the 'summary()' function on the results of also to calculate this

library(tidyverse)
library(datarium) # get another dataset
marketing = as_tibble(marketing)

displayResiduals = function(a, b, x, y) {
  # We can see the 'residual' for each point on the graph
  for(i in 1:length(x))
  {
    cat("Residual #", y[i] - a + b * x[i], "\n") 
  }
}

### TWO WAYS to calculate b 
## Method 1 == Common sense method (range of y over range of x), but less accurate when proceeding to calculate residuals
b = (max(marketing$sales) - min(marketing$sales)) / (max(marketing$youtube) - min(marketing$youtube)) # calculate rise over run // slope
# we got the formula for 'a' by re-arranging y = a + bx
a = mean(marketing$sales) - (b * mean(marketing$youtube)) # calculate y-intercept using slope, mean value of x and mean value of y 

displayResiduals(a, b, marketing$youtube, marketing$sales) # call function to show residuals

## Method 2 == calculus method designed to minimise residuals - more accurate so use this!
b = sum( (marketing$youtube - mean(marketing$youtube)) * (marketing$sales - mean(marketing$sales)) ) / sum( (marketing$youtube - mean(marketing$youtube)) ^ 2)
a = mean(marketing$sales) - (b * mean(marketing$youtube)) # re-calculate y-intercept using slope, mean value of x and mean value of y 

displayResiduals(a, b, marketing$youtube, marketing$sales) # call function to show residuals - they should be smaller!

# Note, we can 'lm()' is used too to carry out regression
model = lm(marketing$sales~marketing$youtube) # automatically calculates y-intercept (a) & slope (b) based the result (sales) and the causing factor (youtube)
a = model$coefficients[1] # index the value returned, first one is a 
b = model$coefficients[2] # second index is b

# We can calculate how two predictor variables (e.g. youtube, facebook) predict sales
model = lm(sales~youtube+facebook,data=marketing) # note, we can just provide the column and specify dataset name after
a = model$coefficients[1]
b = model$coefficients[2]
c = model$coefficients[3]

# Here we can calculate the R-squared to determine which model works best 
modelA = lm(sales~youtube, data=marketing) # calculate intercept, slope
a = modelA$coefficients[1]
b = modelA$coefficients[2]
predicted_salesA = a + b*marketing$youtube #calculate predicted sales based off a and b
residual_salesA = marketing$sales - predicted_sales #calculate the difference between the predicted vs actual results
RSquaredOfModelA = cor(marketing$sales,predicted_salesA)^2 # square the correlation of the residuals to give us R-squared

modelB = lm(marketing$sales~marketing$facebook)
rSquaredB  = summary(modelB)$r.squared # Or, we can calculate this using 'summary()' function

if (rSquaredA > rSquaredB) cat("modelA is a better model than modelB", "\n")
else if (rSquaredB > rSquaredA) cat("modelA is a better model than modelB", "\n")