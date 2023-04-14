import numpy as np
import matplotlib.pyplot as plt
from scipy.integrate import solve_ivp

# Define the Lorenz system
def lorenz_system(t, state, sigma=10, beta=8 / 3, rho=28):
    x, y, z = state
    return [
        sigma * (y - x),
        x * (rho - z) - y,
        x * y - beta * z
    ]

# Reservoir Computer
class ReservoirComputer:
    def __init__(self, input_dim, reservoir_dim, output_dim, spectral_radius=0.95, learning_rate=0.005):
        self.input_dim = input_dim
        self.reservoir_dim = reservoir_dim
        self.output_dim = output_dim
        self.spectral_radius = spectral_radius
        self.learning_rate = learning_rate

        # Initialize reservoir and output weights
        self.Win = np.random.uniform(-0.1, 0.1, (reservoir_dim, input_dim))
        self.W = np.random.uniform(-1, 1, (reservoir_dim, reservoir_dim))
        self.W *= spectral_radius / max(np.abs(np.linalg.eigvals(self.W)))

        self.Wout = np.zeros((output_dim, reservoir_dim))
        self.reservoir_state = np.ones(reservoir_dim)

    def update_reservoir_state(self, reservoir_state, input_signal):
        return np.tanh(np.dot(self.Win, input_signal) + np.dot(self.W, reservoir_state))

    def train_step(self, input_signal, target_signal, ridge_param=0.1):
        reservoir_state = self.update_reservoir_state(self.reservoir_state, input_signal)
        predicted_signal = self.Wout @ reservoir_state
        error = target_signal - predicted_signal

        # Ridge regression update rule
        self.Wout += self.learning_rate * (np.outer(error, reservoir_state) - ridge_param * self.Wout)

        return predicted_signal, error

    def predict(self, input_signal):
        reservoir_state = self.update_reservoir_state(self.reservoir_state, input_signal)
        return np.dot(self.Wout, reservoir_state)

    def reset_state(self):
        self.reservoir_state = np.zeros(self.reservoir_dim)

# Simulate the Lorenz system
t_span = [0, 50]
initial_condition = [1, 1, 1]
t_eval = np.linspace(t_span[0], t_span[1], 5000)
lorenz_states = solve_ivp(lorenz_system, t_span, initial_condition, t_eval=t_eval).y.T

# Initialize reservoir computer
rc = ReservoirComputer(input_dim=3, reservoir_dim=600, output_dim=3)

train_len = int(len(lorenz_states) * 0.8)

# Train reservoir computer
for i in range(train_len - 1):
    rc.train_step(lorenz_states[i], lorenz_states[i + 1])

# Test reservoir computer
rc.reset_state()
predictions = []
for i in range(train_len, len(lorenz_states) - 1):
    prediction = rc.predict(lorenz_states[i])
    predictions.append(prediction)

predictions = np.array(predictions)

# Plot the results
fig, ax = plt.subplots()
ax.plot(t_eval[train_len:], lorenz_states[train_len:, 0], label="Actual")
ax.plot(t_eval[train_len+1:], predictions[:, 0], label="Predicted")
ax.axvline(x=t_eval[train_len] + 1/0.906, color="red", linestyle="--", label="Lyapunov Time")
ax.set_xlabel("Time")
ax.set_ylabel("Variable")
ax.set_title("Reservoir Prediction vs Actual System Value")
ax.legend()

plt.show()