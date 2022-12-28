#pragma once
#include "Model.h"

class ModelManager {
private:
	std::vector<std::shared_ptr<Model>> m_Models;
	int m_SelectedModel;

public:
	ModelManager();
	~ModelManager();

	void AddModel(unsigned int pointIdentifiers,
		const Equation& pointDef,
		unsigned int lineIdentifiers,
		const Equation& lineDef,
		const Equation& incidenceConstr,
		const Equation& betweennessConstr = { {}, "" }) 
	{ 
		m_Models.push_back(std::make_shared<Model>(pointIdentifiers, pointDef, lineIdentifiers, lineDef, incidenceConstr, betweennessConstr));
	}

	std::vector<std::shared_ptr<Model>>& GetModels() { return m_Models; }
	std::shared_ptr<Model> GetModel() { return m_Models[m_SelectedModel]; }
};