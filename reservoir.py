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
        self.Win = np.sqrt(0.002) * np.random.randn(reservoir_dim, input_dim)
        self.W = np.sqrt(2 / reservoir_dim) * np.random.randn(reservoir_dim, reservoir_dim)
        # self.W *= spectral_radius / max(np.abs(np.linalg.eigvals(self.W)))

        self.Wout = np.zeros((output_dim, reservoir_dim))
        self.reservoir_state = np.ones(reservoir_dim)

    def update_reservoir_state(self, reservoir_state, input_signal):
        return np.tanh(np.dot(self.Win, input_signal) + np.dot(self.W, reservoir_state))

    def train_step(self, input_signal, target_signal, ridge_param=0.1):
        reservoir_state = self.update_reservoir_state(self.reservoir_state, input_signal)
        predicted_signal = np.dot(self.Wout, reservoir_state)
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
t_eval = np.linspace(t_span[0], t_span[1], 500)
lorenz_states = solve_ivp(lorenz_system, t_span, initial_condition, t_eval=t_eval).y.T

reservoir_dim = 8

# Initialize reservoir computer
rc = ReservoirComputer(input_dim=3, reservoir_dim=reservoir_dim, output_dim=3)

train_len = int(len(lorenz_states) * 0.5)

# Train reservoir computer
R = np.zeros((reservoir_dim, train_len))
for i in range(train_len):
    rc.reservoir_state = rc.update_reservoir_state(rc.reservoir_state, lorenz_states[i])
    R[:, i] = rc.reservoir_state

ridge_param = 0.01
first_term = lorenz_states[0:train_len].T @ R.T
second_term = np.linalg.inv(R @ R.T + ridge_param * np.eye(reservoir_dim))
rc.Wout = first_term @ second_term

# Test reservoir computer
rc.reset_state()
predictions = []
for i in range(train_len, len(lorenz_states) - 1):
    prediction = rc.predict(lorenz_states[i])
    predictions.append(prediction)
    rc.reservoir_state = rc.update_reservoir_state(rc.reservoir_state, lorenz_states[i+1])

predictions = np.array(predictions)

# Plot the results
fig, ax = plt.subplots()
ax.plot(t_eval[train_len:], lorenz_states[train_len:, 0], label="Actual")
ax.plot(t_eval[train_len+1:], predictions[:, 0], label="Predicted")
ax.axvline(x=t_eval[train_len] + 1/0.906, color="red", linestyle="--", label="Lyapunov Time")
ax.set_xlabel("Time")
ax.set_ylabel("Variable Y")
ax.set_title("Reservoir Prediction vs Actual System Value")
ax.legend()

plt.show()